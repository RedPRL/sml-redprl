functor Compiler (R : REFINER) : COMPILER =
struct
  structure Refiner = R
  structure T = R.Tacticals

  open Abt ScriptOperatorData OperatorData
  infix $ \

  exception MalformedScript of string

  fun pop [] = raise Subscript
    | pop (x :: xs) = (x, xs)

  fun getTerm hasTerm es =
    if hasTerm then
      case es of
          (_ \ m) :: _ => SOME m
         | _ => raise MalformedScript "Expected term argument"
    else
      NONE

  fun getVec m =
    case #1 (infer m) of
         VEC_LIT _ $ es => es
       | _ => raise MalformedScript "Expected vector argument"

  fun mkNameStore xs =
    fn i =>
      List.nth (xs, i)

  (* The idea is to translate scripts like [u... <- elim h; t2]
   * into ML tactics like [Elim h u... THEN t2] *)
  fun go stack m =
    case #1 (infer m) of
         S (BIND _) $ [_ \ t1, e2] =>
           bind stack t1 e2
       | S (ELIM ({target, hasTerm}, _)) $ es =>
           R.Elim target (#1 (pop stack)) (getTerm hasTerm es)
       | S (HYP ({target}, _)) $ _ =>
           R.Hyp target
       | S (INTRO ({rule, hasTerm}, _)) $ es =>
           R.Intro rule (#1 (pop stack)) (getTerm hasTerm es)
       | S (SMASH _) $ [_ \ t1, _ \ t2] =>
           let
             (* below is something very clever / terrifying! *)
             val moduli = map (fn _ => ref 0) stack
             val stack' =
               ListPair.mapEq
                 (fn (r, store) => fn i =>
                   if i + 1 > ! r then
                     (r := i + 1; store i)
                   else
                     store i)
                 (moduli, stack)

             (* We will first compile [t1] such that when it runs, we
              * will covertly observe how much of the name stores it consumes.
              * Then, [t2] will be compiled with all the names [t1] used removed
              * from its name stores. *)
           in
             T.THEN_LAZY
               (go stack' t1,
                fn _ =>
                  let
                    val stack'' =
                      ListPair.mapEq
                        (fn (r, store) => fn i =>
                           store (i + !r))
                        (moduli, stack)
                  in
                    go stack'' t2
                  end)
           end
       | _ => raise MalformedScript "Expected tactical"
  and bind stack t1 ((us, _) \ t2) =
    case #1 (infer t2) of
         S (PAR _) $ [_ \ ts] =>
           T.THENL (go (mkNameStore us :: stack) t1, map (fn (_ \ t) => go stack t) (getVec ts))
       | S (FOCUS {focus}) $ [_ \ t] =>
           T.THENF (go (mkNameStore us :: stack) t1, focus, go stack t)
       | _ =>
           T.THEN (go (mkNameStore us :: stack) t1, go stack t2)

  fun compile m = go [] m

  (* TODO: treat source annotations properly *)
end
