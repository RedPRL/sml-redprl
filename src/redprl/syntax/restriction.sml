structure Restriction :
sig
  (* This structure used to provide functions that automate the
     restriction judgement rules given in "Dependent Cubical
     Realizability", page 46.

     On 2017/06/14, favonia implemented a function to handle
     all cases.
   *)

  (* Restrict a judgement (as the goal) by a list of equations.
   * Returns NONE if the resulting judgement is vacuously true.
   *)
  val restrict : (RedPrlAbt.abt * RedPrlAbt.abt) list -> (RedPrlAbt.abt -> RedPrlAbt.abt) option
end
=
struct
  structure Abt = RedPrlAbt
  structure Syn = SyntaxView
  open Abt

  (* precondition: all term in equations are of sort `DIM` *)
  fun restrict' [] (f : abt -> abt) = SOME f
    | restrict' ((r1, r2) :: eqs) (f : abt -> abt) = 
        (case (Syn.out r1, Syn.out r2) of
            (Syn.DIM0, Syn.DIM0) => restrict' eqs f
          | (Syn.DIM0, Syn.DIM1) => NONE
          | (Syn.DIM1, Syn.DIM1) => restrict' eqs f
          | (Syn.DIM1, Syn.DIM0) => NONE
          | (Syn.VAR (v1, _), _) => if Abt.eq (r1, r2) then restrict' eqs f else substAndRestrict' (r2, v1) eqs f
          | (Syn.META (v1, _), _) => if Abt.eq (r1, r2) then restrict' eqs f else substMetaAndRestrict' (r2, v1) eqs f
          | (_, Syn.VAR (v2, _)) => substAndRestrict' (r1, v2) eqs f
          | (_, Syn.META (v2, _)) => substMetaAndRestrict' (r1, v2) eqs f)

  and substMetaAndRestrict' (r, v) eqs f =
      let
        val abs = abtToAbs r
      in
        restrict'
          (List.map (fn (r1, r2) => (substMetavar (abs, v) r1, substMetavar (abs, v) r2)) eqs)
          (substMetavar (abs, v) o f)
      end

  and substAndRestrict' rv eqs f =
        restrict'
          (List.map (fn (r, r') => (substVar rv r, substVar rv r')) eqs)
          (substVar rv o f)

  fun restrict eqs = restrict' eqs (fn x => x)
end
