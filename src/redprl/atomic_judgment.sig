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

     (* `EQ_TYPE ((a, b), l, k)`:
      *   `a` and `b` are equal types, even taking into the structures
      *   specified by `k`. Both were already defined at the `l'`th iteration
      *   if `l = SOME l'`. If `l = NONE` it means both will be defined
      *   eventually but we do not care about when. For example,
      *   `EQ_TYPE ((a, b), SOME 2, KAN)` means `a` and `b` are equally Kan
      *   in the second iterated type theory.
      *   The realizer is `TV` of sort `TRV`.
      *)
     | EQ_TYPE of abt * abt

     (* `SUB_UNIVERSE (u, l, k)`
      *   `u` is a sub-universe of the universe specified by `l` and `k`.
      *)
     | SUB_UNIVERSE of abt * level * kind

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
  val TYPE : abt -> jdg

  val map : (abt -> abt) -> jdg -> jdg

  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> abt
  val out : abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc
end
