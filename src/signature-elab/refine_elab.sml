structure RefineElab :
sig
  include SIGNATURE_ELAB
  val execute : S2.sign -> (S2.opid * S2.decl -> unit) -> (exn -> unit) -> unit
end =
struct
  structure E = NominalLcfSemantics
  structure S1 = AbtSignature and S2 = AbtSignature
  structure Syn = RedPrlAbtSyntax

  open AbtSignature
  structure T = AbtSignature.Telescope and SD = SortData
  structure Ctx = RefinerKit.Lcf.T

  local
    open RedPrlAbt Sequent
    infix $ $$ \
    infix 4 >>

    structure NameStore = HashTable (structure Key = IntHashable)

    fun makeNameStore () =
      let
        val cache = NameStore.table 255
      in
        fn i =>
          case NameStore.find cache i of
               NONE =>
                 let
                   val x = Symbol.named ("@" ^ Int.toString i)
                 in
                   (NameStore.insert cache i x; x)
                 end
             | SOME x => x
      end

    fun errorMessage pos msg =
      Pos.toString pos ^ ": " ^ msg
  in
    fun elabThm sign (d as {parameters, arguments, sort, definiens}, pos) : decl =
      case Syn.out definiens of
           Syn.REFINE_SCRIPT (tau, prop, script, extract) =>
             (* If an extract has already been computed, then skip; otherwise
              * we run the proof script to compute its extract. *)
             (case Syn.out extract of
                  Syn.OPT_SOME _ => def sign (d, pos)
                | Syn.OPT_NONE _ =>
                    let
                      val alpha = makeNameStore ()
                      val goal = emptyContext >> TRUE (prop, tau)
                      val st as (psi, vld) = E.tactic (sign, Variable.Ctx.empty) script alpha goal
                    in
                      case Ctx.ConsView.out psi of
                           Ctx.ConsView.EMPTY =>
                             let
                               val _ \ evd = outb (vld Ctx.empty)
                               val evd' = Syn.into (Syn.OPT_SOME (tau, evd))
                               val prf = Syn.into (Syn.REFINE_SCRIPT (tau, prop, script, evd'))
                             in
                               def sign
                                 ({parameters = parameters,
                                   arguments = arguments,
                                   sort = sort,
                                   definiens = prf},
                                  pos)
                             end
                         | _ =>
                           let
                             val proofState = RefinerKit.Tacticals.Lcf.stateToString st
                           in
                             raise RedPrlExn.RedPrlExn (pos, "Refinement Failed\n\n" ^ proofState)
                           end
                      end
                  | _ => raise RedPrlExn.RedPrlExn (pos, "Expected either OP_SOME or OP_NONE"))
         | _ => def sign (d, pos) handle exn => raise RedPrlExn.wrap pos exn
  end

  fun elab sign (d, pos) : decl =
    case #sort d of
         SD.THM tau => elabThm sign (d, pos)
       | _ => def sign (d, pos)

  fun transport sign =
    let
      open T.ConsView
      fun go res =
        fn EMPTY => res
         | CONS (x, (Decl.DEF d, pos), xs) => go (T.snoc res x (elab res (d, pos), pos)) (out xs)
         | CONS (x, (Decl.SYM_DECL tau, pos), xs) => go (T.snoc res x (Decl.SYM_DECL tau, pos)) (out xs)
    in
      go T.empty (out sign)
    end

  fun execute sign succeed fail =
    let
      open T.ConsView
      fun go res =
        fn EMPTY => ()
         | CONS (x, (Decl.DEF d, pos), xs) =>
             (let
                val res' =
                  let
                    val d' = elab res (d, pos)
                  in
                    succeed (x, d');
                    T.snoc res x (d', pos)
                  end handle exn => (fail exn; res)
              in
                go res' (out xs)
              end)
        | CONS (x, (d as Decl.SYM_DECL tau, pos), xs) =>
            (succeed (x, d);
             go (T.snoc res x (d, pos)) (out xs))
    in
      go T.empty (out sign)
    end
end
