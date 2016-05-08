structure RefineElab : SIGNATURE_ELAB =
struct
  structure E = NominalLcfSemantics
  structure S1 = AbtSignature and S2 = AbtSignature

  open AbtSignature
  structure T = AbtSignature.Telescope and SD = SortData
  structure Ctx = RefinerKit.Lcf.T

  exception hole
  fun ?e = raise e

  local
    open Abt OperatorData Sequent infix $ \
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
      case out definiens of
           REFINE tau $ [_ \ prop, _ \ script, _ \ extract] =>
             (* If an extract has already been computed, then skip; otherwise
              * we run the proof script to compute its extract. *)
             (case out extract of
                   OP_SOME _ $ _ => def sign d
                 | OP_NONE _ $ _ =>
                     let
                       val alpha = makeNameStore ()
                       val goal = emptyContext >> TRUE (prop, tau)
                       val st as (psi, vld) = E.tactic (sign, Variable.Ctx.empty) script alpha goal
                     in
                       case Ctx.ConsView.out psi of
                            Ctx.ConsView.EMPTY =>
                              let
                                val _ \ evd = outb (vld Ctx.empty)
                                val evd' = check (OP_SOME tau $ [([],[]) \ evd], SortData.OPT tau)
                                val prf = check (REFINE tau $ [([],[]) \ prop, ([],[]) \ script, ([],[]) \ evd'], SortData.THM tau)
                              in
                                def sign
                                  {parameters = parameters,
                                   arguments = arguments,
                                   sort = sort,
                                   definiens = prf}
                              end
                          | _ => raise Fail
                                   ("Incomplete proof:\n\n"
                                      ^ RefinerKit.Tacticals.Lcf.stateToString st
                                      ^ "\n\n")
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
