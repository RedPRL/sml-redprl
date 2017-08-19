structure RedPrlCategoricalJudgmentData =
struct
  type kind = RedPrlKind.t

  datatype ('sym, 'a) jdg' =

   (* `EQ ((m, n), (a, k))`:
    *   `EQ_TYPE ((a, a), k)` and `m` and `n` are related by the PER associated with `a`.
    *   The realizer is `TV` of sort `TRIV`.
    *)
     EQ of ('a * 'a) * ('a * kind)

   (* `TRUE (a, k)`:
    *   `EQ_TYPE ((a, a), k)` and there exists a term `m` such that
    *   `EQ ((m, m), (a, k))` is provable.
    *   The realizer is such an `m` of sort `EXP`.
    *)
   | TRUE of 'a * kind

   (* `EQ_TYPE ((a, b), k)`:
    *   `a` and `b` are equal types, taking into account the additional
    *   structures specified by `k`. For example, `EQ_TYPE ((a, b), KAN)`
    *   means they are equally Kan, in addition to being equal pretypes.
    *   The realizer is `TV` of sort `TRIV`.
    *)
   | EQ_TYPE of ('a * 'a) * kind

   (* `TERM tau`:
    *   There exists some `m` of sort `tau`.
    *   The realizer is such an `m` of sort `tau`.
    *)
   | SYNTH of 'a * kind

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
   | PARAM_SUBST of ('a * RedPrlParamSort.t * 'sym) list * 'a * RedPrlSort.t
end

signature CATEGORICAL_JUDGMENT =
sig
  datatype jdg' = datatype RedPrlCategoricalJudgmentData.jdg'
  val MEM : 'a * ('a * RedPrlKind.t) -> ('sym, 'a) jdg'
  val TYPE : 'a * RedPrlKind.t -> ('sym, 'a) jdg'

  val map' : ('sym1 -> 'sym2) -> ('term1 -> 'term2)
    -> ('sym1, 'term1) jdg' -> ('sym2, 'term2) jdg'
  val map : ('term1 -> 'term2) -> ('sym, 'term1) jdg' -> ('sym, 'term2) jdg'

  (* Pretty printer *)
  val pretty' : ('sym -> Fpp.doc) -> ('term -> Fpp.doc) -> ('term * 'term -> bool)
    -> ('sym, 'term) jdg' -> Fpp.doc

  (* Functions for abt *)
  type jdg = (Sym.t, RedPrlAbt.abt) jdg'
  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> RedPrlAbt.abt
  val out : RedPrlAbt.abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc

  (* Functions for ast *)
  type astjdg = (string, RedPrlAst.ast) jdg'
  val astOut : RedPrlAst.ast -> astjdg
end
