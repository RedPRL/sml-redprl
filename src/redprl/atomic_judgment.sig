structure RedPrlAtomicJudgmentData =
struct
  type kind = RedPrlKind.t

  structure Tm = RedPrlAbt

  local
    open Tm
  in
    datatype jdg =

     (* `EQ ((m, n), a)`:
      *   The term `a` was associated with a PER and terms `m` and `n` were
      *   related by that PER.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
       EQ of (abt * abt) * abt

     (* `TRUE a`:
      *   The term `a` was associated with a PER and there existed a term `m`
      *   such that `m` was related to itself in that PER.
      *
      *   The realizer is such an `m` of sort `EXP`.
      *)
     | TRUE of abt

     (* `EQ_TYPE ((a, b), k)`:
      *   The terms `a` and `b` are equal types and have equal structures
      *   specified by `k`. This implies they have the same PER.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
     | EQ_TYPE of (abt * abt) * kind

     (* `SUB_TYPE (a, b)`:
      *   The terms `a` and `b` are types and the PER associated with `a`
      *   is a subrelation of the PER associated with `b`.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
     | SUB_TYPE of (abt * abt)

     (* `SUB_UNIVERSE (a, k)`
      *   `a` is a sub-universe of U^`k`.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
     | SUB_UNIVERSE of abt * kind

     (* `SYNTH a`:
      *   There existed a term `a` associated with a PER and the term `m`
      *   was related to itself in that PER.
      *
      *   The realizer is such an `a` of sort `exp`.
      *)
     | SYNTH of abt

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
  type kind = RedPrlKind.t

  val TYPE : abt * RedPrlKind.t -> jdg
  val MEM : abt * abt -> jdg

  val map : (abt -> abt) -> jdg -> jdg

  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> abt
  val out : abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc
end
