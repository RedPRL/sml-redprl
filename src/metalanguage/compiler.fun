functor Compiler (R : REFINER) : COMPILER =
struct
  structure Refiner = R
  structure T = R.Tacticals

  open Abt ScriptOperatorData OperatorData
  infix $ \

  exception MalformedScript

  fun pop [] = raise Subscript
    | pop (x :: xs) = x

  fun getTerm hasTerm es =
    if hasTerm then
      case es of
          (_ \ m) :: _ => SOME m
         | _ => raise MalformedScript
    else
      NONE

  (* The idea is to translate scripts like [u... <- elim h; t2]
   * into ML tactics like [Elim h u... THEN t2] *)
  fun go stack m =
    case #1 (infer m) of
         S (THEN _) $ [_ \ t1, (us, _) \ t2] =>
           T.THEN (go (us :: stack) t1, go stack t2)
       | S (ELIM ({target, hasTerm}, _)) $ es =>
           R.Elim target (pop stack) (getTerm hasTerm es)
       | S (HYP ({target}, _)) $ _ =>
           R.Hyp target
       | S (INTRO ({rule, hasTerm}, _)) $ es =>
           R.Intro rule (getTerm hasTerm es)
       | _ => raise MalformedScript

  fun compile m = go [] m

  (* TODO: treat source annotations properly *)
end
