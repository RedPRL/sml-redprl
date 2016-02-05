signature LCF_ELABORATOR' =
  LCF_ELABORATOR
    where type Signature.Abt.abt = Abt.abt
    where type 'i Signature.Abt.Operator.t = 'i Operator.t
    where type Signature.Abt.Operator.Arity.Valence.Sort.t = Sort.t
    where type 'a Signature.Abt.Operator.Arity.Valence.Spine.t = 'a list
    where type Refiner.Tacticals.Lcf.judgment = Sequent.sequent
    where type Refiner.Tacticals.Lcf.evidence = Abt.abt
    where type 'a Refiner.Tacticals.Lcf.ctx = 'a SymbolTelescope.telescope

functor RefineElab (E : LCF_ELABORATOR') : SIGNATURE_ELAB =
struct
  structure S1 = E.Signature and S2 = E.Signature

  open E E.Signature
  structure T = Signature.Telescope and SD = SortData and ST = SymbolTelescope

  exception hole
  fun ?e = raise e

  local
    open Abt OperatorData Sequent infix $ \ >>

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
           PROVE $ [_ \ prop, _ \ script, _ \ extract] =>
             (* If an extract has already been computed, then skip; otherwise
              * we run the proof script to compute its extract. *)
             (case out extract of
                   OP_SOME _ $ _ => def sign d
                 | OP_NONE _ $ _ =>
                     let
                       val alpha = makeNameStore ()
                       val goal = ST.empty >> prop
                       val (psi, vld) = E.elaborate' sign script alpha goal
                     in
                       case ST.ConsView.out psi of
                            ST.ConsView.Empty =>
                              let
                                val phi = metactx definiens
                                val evd = vld (ST.empty)
                                val prf = PROVE $ [([],[]) \ prop, ([],[]) \ script, ([],[]) \ evd]
                              in
                                def sign
                                  {parameters = parameters,
                                   arguments = arguments,
                                   sort = sort,
                                   definiens = check phi (prf, SortData.THM)}
                              end
                          | _ => raise Fail "Incomplete proof" (* TODO: print subgoals *)
                     end
                 | _ => raise Fail "Expected either OP_SOME or OP_NONE")
         | _ => def sign d
  end

  fun elab sign d : decl =
    case #sort d of
         SD.THM => elabThm sign d
       | _ => def sign d


  fun transport sign =
    let
      open T.ConsView
      fun go res =
        fn Empty => res
         | Cons (x,d,xs) => go (T.snoc res (x, elab res (undef d))) (out xs)
    in
      go T.empty (out sign)
    end
end
