structure RefineElab : SIGNATURE_ELAB =
struct
  structure E = NominalLcfSemantics
  structure S1 = AbtSignature and S2 = AbtSignature
  structure Syn = RedPrlAbtSyntax

  open AbtSignature
  structure T = AbtSignature.Telescope and SD = SortData
  structure Ctx = RefinerKit.Lcf.T

  datatype 'a elab_result =
      SUCCESS of 'a
    | FAILURE of Pos.t option * string

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
    fun elabThm sign (d as {parameters, arguments, sort, definiens}) : decl elab_result =
      case Syn.out definiens of
           Syn.REFINE_SCRIPT (tau, prop, script, extract) =>
             let
               val pos = Abt.getAnnotation script
             in
               (* If an extract has already been computed, then skip; otherwise
                * we run the proof script to compute its extract. *)
               (case Syn.out extract of
                    Syn.OPT_SOME _ => SUCCESS (def sign d)
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
                                 SUCCESS
                                   (def sign
                                     {parameters = parameters,
                                      arguments = arguments,
                                      sort = sort,
                                      definiens = prf})
                               end
                           | _ =>
                             let
                               val annotation : Pos.t option = Abt.getAnnotation script
                               val proofState = RefinerKit.Tacticals.Lcf.stateToString st
                             in
                               FAILURE (pos, "Refinement Failed\n\n" ^ RefinerKit.Tacticals.Lcf.stateToString st)
                             end
                        end
                    | _ => FAILURE (pos, "Expected either OP_SOME or OP_NONE"))
                  handle Fail msg => FAILURE (pos, msg)
                       | NominalLcfModel.RefinementError (pos, exn) => FAILURE (pos, exnMessage exn)
                       | exn => FAILURE (pos, exnMessage exn)
             end
         | _ =>
           let
             val pos = Abt.getAnnotation definiens
           in
             SUCCESS (def sign d)
               handle Fail msg => FAILURE (pos, msg)
                    | exn => FAILURE (pos, exnMessage exn)
           end
  end

  fun elab sign d : decl elab_result =
    case #sort d of
         SD.THM tau => elabThm sign d
       | _ => SUCCESS (def sign d)

  fun transport sign =
    let
      open T.ConsView
      fun go res =
        fn EMPTY => res
         | CONS (x, Decl.DEF d,xs) =>
             (case elab res d of
                  SUCCESS d' => go (T.snoc res x d') (out xs)
                | FAILURE (pos, msg) =>
                    let
                      fun printErr str = TextIO.output (TextIO.stdErr, str)
                      val pos =
                        case pos of
                           SOME pos => pos
                         | NONE => Pos.pos (Coord.init "-") (Coord.init "-")
                      val errorMessage = Pos.toString pos ^ ": " ^ msg
                    in
                      printErr errorMessage;
                      OS.Process.exit OS.Process.failure
                    end)
         | CONS (x, Decl.SYM_DECL tau, xs) => go (T.snoc res x (Decl.SYM_DECL tau)) (out xs)
    in
      go T.empty (out sign)
    end
end
