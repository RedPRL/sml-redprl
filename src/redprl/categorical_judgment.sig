structure RedPrlCategoricalJudgmentData =
struct
  type kind = RedPrlKind.t

  datatype ('sym, 'level, 'term) jdg' =

   (* `EQ ((m, n), (a, l, k))`:
    *   `EQ_TYPE ((a, a), l, k)` and `m` and `n` are related by the PER
    *   associated with `a`. Moreover, `a` was already defined at the
    *   `l'`th iteration if `l = SOME l'`. If `l = NONE` it means `a`
    *   was defined at some level but we do not care.
    *   The realizer is `TV` of sort `TRIV`.
    *)
     EQ of ('term * 'term) * ('term * 'level * kind)

   (* `TRUE (a, l, k)`:
    *   `EQ_TYPE ((a, a), l, k)` and there exists a term `m` such that
    *   `EQ ((m, m), (a, l, k))` is provable.
    *   The realizer is such an `m` of sort `EXP`.
    *)
   | TRUE of 'term * 'level * kind

   (* `EQ_TYPE ((a, b), l, k)`:
    *   `a` and `b` are equal types, even taking into the structures
    *   specified by `k`. Both were already defined at the `l'`th iteration
    *   if `l = SOME l'`. If `l = NONE` it means both will be defined
    *   eventually but we do not care about when. For example,
    *   `EQ_TYPE ((a, b), SOME 2, KAN)` means `a` and `b` are equally Kan
    *   in the second iterated type theory.
    *   The realizer is `TV` of sort `TRIV`.
    *)
   | EQ_TYPE of ('term * 'term) * 'level * kind

   (* `SUB_UNIVERSE (u, l, k)`
    *   `u` is a sub-universe of the universe specified by `l` and `k`.
    *)
   | SUB_UNIVERSE of 'term * 'level * kind

   (* `TERM tau`:
    *   There exists some `m` of sort `tau`.
    *   The realizer is such an `m` of sort `tau`.
    *)
   | SYNTH of 'term * 'level * kind

   (* `TERM tau`:
    *   There exists some `m` of sort `tau`.
    *   The realizer is such an `m` of sort `tau`.
    *)
   | TERM of RedPrlSort.t

   (* `PARAM_SUBST (l, m, s)`:
    *   `l` is a list of elements of shape `(pe, ps, r)`, representing a
    *   parameter substitution, where `pe` will (eventually) be `PARAM_EXP p`
    *   for some parameter term `p`, `r` is a parameter variable and `ps` is
    *   the sort of `p` and `r`. `m` is an expression of sort `s`.
    *   The realizer is the result of applying the substitution `l` to `m`.
    *)
   | PARAM_SUBST of ('term * RedPrlParamSort.t * 'sym) list * 'term * RedPrlSort.t
end

signature CATEGORICAL_JUDGMENT =
sig
  datatype jdg' = datatype RedPrlCategoricalJudgmentData.jdg'
  val MEM : 'term * ('term * 'level * RedPrlKind.t) -> ('sym, 'level, 'term) jdg'
  val TYPE : 'term * 'level * RedPrlKind.t -> ('sym, 'level, 'term) jdg'

  val map'
    : ('sym1 -> 'sym2)
    -> ('level1 -> 'level2)
    -> ('term1 -> 'term2)
    -> ('sym1, 'level1, 'term1) jdg'
    -> ('sym2, 'level2, 'term2) jdg'
  val map : ('term1 -> 'term2) -> ('sym, 'level, 'term1) jdg' -> ('sym, 'level, 'term2) jdg'

  (* raw pretty printer *)
  val pretty'
    : ('sym -> Fpp.doc)
    -> ('level -> Fpp.doc)
    -> ('term -> Fpp.doc)
    -> ('term * 'term -> bool)
    -> ('sym, 'level option, 'term) jdg'
    -> Fpp.doc

  (* functions for judgments based on abt *)
  type jdg = (Sym.t, RedPrlLevel.P.level, RedPrlAbt.abt) jdg'
  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> RedPrlAbt.abt
  val out : RedPrlAbt.abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc

  (* functions for judgments based on ast *)
  type astjdg = (string, RedPrlAstLevel.P.level, RedPrlAst.ast) jdg'
  val astOut : RedPrlAst.ast -> astjdg
end
