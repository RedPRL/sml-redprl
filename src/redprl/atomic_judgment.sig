structure RedPrlAtomicJudgmentData =
struct
  type kind = RedPrlKind.t
  type level = RedPrlLevel.t

  structure Tm = RedPrlAbt

  local
    open Tm
  in
    datatype jdg =

     (* `EQ ((m, n), (a, l, k))`:
      *   `EQ_TYPE ((a, a), l, k)` and `m` and `n` are related by the PER
      *   associated with `a`. Moreover, `a` was already defined at the
      *   `l'`th iteration if `l = SOME l'`. If `l = NONE` it means `a`
      *   was defined at some level but we do not care.
      *   The realizer is `TV` of sort `TRV`.
      *)
       EQ of (abt * abt) * abt

     (* `TRUE (a, l, k)`:
      *   `EQ_TYPE ((a, a), l, k)` and there exists a term `m` such that
      *   `EQ ((m, m), (a, l, k))` is provable.
      *   The realizer is such an `m` of sort `EXP`.
      *)
     | TRUE of abt

     (* `TERM tau`:
      *   There exists some `m` of sort `tau`.
      *   The realizer is such an `m` of sort `tau`.
      *)
     | SYNTH of abt

     (* `TERM tau`:
      *   There exists some `m` of sort `tau`.
      *   The realizer is such an `m` of sort `tau`.
      *)
     | TERM of sort
  end
end

signature CATEGORICAL_JUDGMENT =
sig
  datatype jdg = datatype RedPrlAtomicJudgmentData.jdg
  type abt = RedPrlAbt.abt
  type level = RedPrlLevel.t
  type kind = RedPrlKind.t

  val MEM : abt * abt -> jdg

  val map : (abt -> abt) -> jdg -> jdg

  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> abt
  val out : abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc
end
