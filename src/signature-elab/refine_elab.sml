structure RefineElab : SIGNATURE_ELAB =
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
  in
    fun elabThm sign (d as {parameters, arguments, sort, definiens}) : decl =
      case Syn.out definiens of
           Syn.REFINE_SCRIPT (tau, prop, script, extract) =>
             (* If an extract has already been computed, then skip; otherwise
              * we run the proof script to compute its extract. *)
             (case Syn.out extract of
                   Syn.OPT_SOME _ => def sign d
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
                                  {parameters = parameters,
                                   arguments = arguments,
                                   sort = sort,
                                   definiens = prf}
                              end
                          | _ =>
                            let
                              val annotation : Pos.t option = Abt.getAnnotation script
                              val proofState = RefinerKit.Tacticals.Lcf.stateToString st
                              val location =
                                  case Abt.getAnnotation script of
                                      SOME pos => Pos.toString pos
                                   |  NONE => "unknown location"
                            in
                              raise Fail ("Incomplete proof @ " ^ location ^ ":\n\n" ^ RefinerKit.Tacticals.Lcf.stateToString st ^ "\n\n")
                            end
                     end
                 | _ => raise Fail "Expected either OP_SOME or OP_NONE")
         | _ => def sign d
  end

  fun elab sign d : decl =
    case #sort d of
         SD.THM tau => elabThm sign d
       | _ => def sign d


  fun transport sign =
    let
      open T.ConsView
      fun go res =
        fn EMPTY => res
         | CONS (x, Decl.DEF d,xs) => go (T.snoc res x (elab res d)) (out xs)
         | CONS (x, Decl.SYM_DECL tau, xs) => go (T.snoc res x (Decl.SYM_DECL tau)) (out xs)
    in
      go T.empty (out sign)
    end
end
