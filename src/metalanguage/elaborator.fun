functor Elaborator (R : REFINER) : ELABORATOR =
struct
  structure Refiner = R
  structure T = R.Tacticals

  open Abt ScriptOperatorData OperatorData SortData
  infix $ \

  exception MalformedScript of string

  fun pop [] = raise Subscript
    | pop (x :: xs) = x

  fun mkNameStore xs =
    fn i =>
      List.nth (xs, i)

  fun elaborateOpt m =
    case infer m of
         (OP_SOME _ $ [_ \ n], OPT _) => SOME n
       | (OP_NONE _ $ _, OPT _) => NONE
       | _ => raise MalformedScript "Expected SOME or NONE"

  fun elaborateVec m =
    case #1 (infer m) of
         VEC_LIT _ $ es => List.map (fn (_ \ n) => n) es
       | _ => raise MalformedScript "Expected vector argument"


  (* The idea is to translate scripts like [u... <- elim h; t2]
   * into ML tactics like [Elim h u... THEN t2] *)
  fun go stack m =
    case #1 (infer m) of
         S (BIND _) $ [_ \ t1, e2] =>
           bind stack t1 e2
       | S (ELIM ({target}, _)) $ [_ \ m] =>
           R.Elim target (pop stack) (elaborateOpt m)
       | S (HYP ({target}, _)) $ _ =>
           R.Hyp target
       | S (INTRO ({rule}, _)) $ [_ \ m] =>
           R.Intro rule (pop stack) (elaborateOpt m)
       | S (SMASH _) $ [_ \ t1, _ \ t2] =>
           let
             (* below is something very clever / terrifying! *)
             val moduli = map (fn _ => ref 0) stack
             val stack' =
               ListPair.mapEq
                 (fn (m, store) => fn i =>
                   if i + 1 > ! m then
                     (m := i + 1; store i)
                   else
                     store i)
                 (moduli, stack)

             (* We will first elaborate [t1] such that when it runs, we
              * will covertly observe how much of the name stores it consumes.
              * Then, [t2] will be elaborated with all the names [t1] used removed
              * from its name stores. *)
           in
             T.THEN_LAZY
               (go stack' t1,
                fn _ =>
                  let
                    val stack'' =
                      ListPair.mapEq
                        (fn (m, store) => fn i =>
                           store (i + !m))
                        (moduli, stack)
                  in
                    go stack'' t2
                  end)
           end
       | _ => raise MalformedScript "Expected tactical"

  and bind stack t1 ((us, _) \ t2) =
    case #1 (infer t2) of
         S (MULTI _) $ [_ \ ts] =>
           T.THENL (go (mkNameStore us :: stack) t1, map (go stack) (elaborateVec ts))
       | S (FOCUS {focus}) $ [_ \ t] =>
           T.THENF (go (mkNameStore us :: stack) t1, focus, go stack t)
       | _ =>
           T.THEN (go (mkNameStore us :: stack) t1, go stack t2)

  fun elaborate m = go [] m

  (* TODO: treat source annotations properly *)
end
