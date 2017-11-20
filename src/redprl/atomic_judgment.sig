structure RedPrlAtomicJudgmentData =
struct
  type kind = RedPrlKind.t
  type level = RedPrlLevel.t

  structure Tm = RedPrlAbt

  local
    open Tm
  in
    datatype jdg =

     (* `EQ ((m, n), (a, l))`:
      *   Already in the `l`th iteration of universe hierarchy construction,
      *   the term `a` was associated with a PER and terms `m` and `n` were
      *   related by that PER.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
       EQ of (abt * abt) * (abt * level)

     (* `TRUE (a, l)`:
      *   Already in the `l`th iteration of universe hierarchy construction,
      *   the term `a` was associated with a PER and there existed a term `m`
      *   such that `m` was related to itself in that PER.
      *
      *   The realizer is such an `m` of sort `EXP`.
      *)
     | TRUE of abt * level

     (* `SUB_TYPE ((a, b), l, k)`
      *   Already in the `l`th iteration of universe hierarchy construction,
      *   `a` is a subtype of `b`. The RedPRL proof theory is intentionally
      *   weak so that there are only a few provable instances of non-trivial
      *   subtyping.
      *)
     | SUB_TYPE of (abt * abt) * level * kind

     (* `SYNTH (m, l)`:
      *   Already in the `l`th iteration of universe hierarchy construction,
      *   there existed a term `a` associated with a PER and the term `m`
      *   was related to itself in that PER.
      *
      *   The realizer is such an `a` of sort `exp`.
      *)
     | SYNTH of abt * level

     (* `TERM tau`:
      *   There exists some term `m` of sort `tau`.
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

  val MEM : abt * (abt * level) -> jdg

  val map : (abt -> abt) -> jdg -> jdg

  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> abt
  val out : abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc
end
