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
    infix 3 |>

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
                       val context =
                         {metactx = List.foldl (fn ((x,vl), psi) => MetaCtx.insert psi x vl) MetaCtx.empty arguments,
                          symctx = List.foldl (fn ((u,tau), upsilon) => SymCtx.insert upsilon u tau) SymCtx.empty parameters,
                          hypctx = SymbolTelescope.empty}
                       val goal = [] |> context >> TRUE (prop, tau)
                       val st as (psi, vld) = E.tactic (sign, VarCtx.empty) script alpha goal
                     in
                       case Ctx.ConsView.out psi of
                            Ctx.ConsView.EMPTY =>
                              let
                                val phi = metactx definiens
                                val _ \ evd = outb (vld Ctx.empty)
                                val evd' = check phi (OP_SOME tau $ [([],[]) \ evd], SortData.OPT tau)
                                val prf = REFINE tau $ [([],[]) \ prop, ([],[]) \ script, ([],[]) \ evd']
                              in
                                def sign
                                  {parameters = parameters,
                                   arguments = arguments,
                                   sort = sort,
                                   definiens = check phi (prf, SortData.THM tau)}
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
         | CONS (x, Decl.SYMDCL tau, xs) => go (T.snoc res x (Decl.SYMDCL tau)) (out xs)
    in
      go T.empty (out sign)
    end
end
