structure Restriction :
sig
  (* This structure used to provide functions that automate the
     restriction judgement rules given in "Dependent Cubical
     Realizability", page 46.

     On 2017/06/14, favonia implemented a function to handle
     all cases.
   *)

  (* 2018/04/19 favonia
   *
   * Consider the following two restricted judgments:
   *
   * i:dim, x:A_i, j:dim >> J [i=j]
   * j:dim, x:A_j, i:dim >> J [i=j]
   *
   * The correct substitution for `[i=j]` has to take the variable
   * ordering in the context into consideration.
   *)

  (* Restrict a judgement (as the goal) by a list of equations.
   * Returns NONE if the resulting judgement is vacuously true.
   *)
  val restrict : Sequent.hyps
    -> (RedPrlAbt.abt * RedPrlAbt.abt) list
    -> (RedPrlAbt.abt -> RedPrlAbt.abt) option
  (* This variant gives the caller an opportunity to pre-compute the ordering.
   * The numbers associated with the variables in the context should be strictly
   * increasing from left to right. *)
  val restrictWithOrder : int Sym.Ctx.dict
    -> (RedPrlAbt.abt * RedPrlAbt.abt) list
    -> (RedPrlAbt.abt -> RedPrlAbt.abt) option
end
=
struct
  structure Abt = RedPrlAbt
  structure Syn = SyntaxView
  open Abt

  val createOrderMapping : Sequent.hyps -> int Sym.Ctx.dict
    = #1 o Sequent.Hyps.foldl (fn (v, _, (d, s)) => (Sym.Ctx.insert d v s, s + 1)) (Sym.Ctx.empty, 0)

  (* precondition: all term in equations are of sort `DIM` *)
  fun restrict' order [] (f : abt -> abt) = SOME f
    | restrict' order ((r1, r2) :: eqs) (f : abt -> abt) =
        (case (Syn.out r1, Syn.out r2) of
            (Syn.DIM0, Syn.DIM0) => restrict' order eqs f
          | (Syn.DIM0, Syn.DIM1) => NONE
          | (Syn.DIM1, Syn.DIM1) => restrict' order eqs f
          | (Syn.DIM1, Syn.DIM0) => NONE
          | (Syn.META (v1, _), _) => if Abt.eq (r1, r2) then restrict' order eqs f else substMetaAndRestrict' order (r2, v1) eqs f
          | (_, Syn.META (v2, _)) => substMetaAndRestrict' order (r1, v2) eqs f
          | (Syn.VAR (v1, _), Syn.VAR (v2, _)) => if Abt.eq (r1, r2) then restrict' order eqs f else mergeVarsAndRestrict' order (v1, v2) eqs f
          | (Syn.VAR (v1, _), _) => if Abt.eq (r1, r2) then restrict' order eqs f else substAndRestrict' order (r2, v1) eqs f
          | (_, Syn.VAR (v2, _)) => substAndRestrict' order (r1, v2) eqs f)

  and substMetaAndRestrict' order (r, v) eqs f =
      let
        val abs = abtToAbs r
      in
        restrict' order
          (List.map (fn (r1, r2) => (substMetavar (abs, v) r1, substMetavar (abs, v) r2)) eqs)
          (substMetavar (abs, v) o f)
      end

  and mergeVarsAndRestrict' order (v1, v2) eqs f =
      let
        val (v1, v2) =
          if Sym.Ctx.lookup order v1 <= Sym.Ctx.lookup order v2 then
            (v1, v2)
          else
            (v2, v1)
      in
        restrict' order
          (List.map (fn (r, r') => (VarKit.rename (v2, v1) r, VarKit.rename (v2, v1) r')) eqs)
          (VarKit.rename (v2, v1) o f)
      end

  and substAndRestrict' order rv eqs f =
        restrict' order
          (List.map (fn (r, r') => (substVar rv r, substVar rv r')) eqs)
          (substVar rv o f)

  fun restrictWithOrder order eqs = restrict' order eqs (fn x => x)
  fun restrict hyps = restrictWithOrder (createOrderMapping hyps)
end
