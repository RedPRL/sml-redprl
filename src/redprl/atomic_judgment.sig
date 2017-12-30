structure RedPrlAtomicJudgmentData =
struct
  type kind = RedPrlKind.t

  structure Tm = RedPrlAbt

  local
    open Tm
  in
    datatype jdg =

     (* `EQ ((m, n), a)`:
      *   The term `a` was associated with a PER and terms `m` and `n` are
      *   related by that PER.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
       EQ of (abt * abt) * abt

     (* `TRUE a`:
      *   The term `a` is associated with a PER and there exists a term `m`
      *   such that `m` is related to itself in that PER.
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

     (* `SUB_KIND (a, k)`
      *   `a` is a sub-universe of the universe of `k` types at the omega level.
      *
      *   The realizer is `TV` of sort `TRV`.
      *)
     | SUB_KIND of abt * kind

     (* `SYNTH m`:
      *   There exists a term `a` associated with a PER and the term `m`
      *   is related to itself by that PER.
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

  (* favonia: I do not like the current usage of "invariant" in many PLs,
   *          so I coined the word "anti-variant". *)
  datatype variance = COVAR | CONTRAVAR | ANTIVAR
end

signature CATEGORICAL_JUDGMENT =
sig
  datatype jdg = datatype RedPrlAtomicJudgmentData.jdg
  datatype variance = datatype RedPrlAtomicJudgmentData.variance
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

  val variance : jdg * RedPrlOpData.accessor -> variance

  (* TODO move composeVariance to somewhere else? *)
  val composeVariance : variance * variance -> variance
end
