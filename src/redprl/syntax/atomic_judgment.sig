structure AtomicJudgmentData =
struct
  type kind = RedPrlKind.t
  type abt = RedPrlAbt.abt
  type sort = RedPrlSort.sort

  datatype jdg =

    (* `TRUE a`:
    *   The term `a` is associated with a PER and there exists a term `m`
    *   such that `m` is related to itself in that PER.
    *
    *   The realizer is such an `m` of sort `EXP`.
    *)
      TRUE of abt

    (* `EQ_TYPE ((a, b), k)`:
    *   The terms `a` and `b` are equal types and have equal structures
    *   specified by `k`. This implies they have the same PER.
    *
    *   The realizer is `AX` of sort `EXP`.
    *)
    | EQ_TYPE of (abt * abt) * kind

    (* `SUB_TYPE (a, b)`:
    *   The terms `a` and `b` are types and the PER associated with `a`
    *   is a subrelation of the PER associated with `b`.
    *
    *   The realizer is `AX` of sort `EXP`.
    *)
    | SUB_TYPE of (abt * abt)

    (* `SUB_KIND (a, k)`
    *   `a` is a sub-universe of the universe of `k` types at the omega level.
    *
    *   The realizer is `AX` of sort `EXP`.
    *)
    | SUB_KIND of abt * kind

    (* `TERM tau`:
    *   There exists some term `m` of sort `tau`.
    *   The realizer is such an `m` of sort `tau`.
    *)
    | TERM of sort
end

signature ATOMIC_JUDGMENT =
sig
  datatype jdg = datatype AtomicJudgmentData.jdg
  type abt = RedPrlAbt.abt
  type kind = RedPrlKind.t

  val TYPE : abt * RedPrlKind.t -> jdg
  val EQ : (abt * abt) * abt -> jdg
  val MEM : abt * abt -> jdg

  val map : (abt -> abt) -> jdg -> jdg

  val synthesis : jdg -> RedPrlAbt.sort
  val into : jdg -> abt
  val out : abt -> jdg
  val eq : jdg * jdg -> bool
  val pretty : jdg -> Fpp.doc
  val pretty' : TermPrinter.env -> jdg -> Fpp.doc

  val lookupAccessor : Accessor.t -> jdg -> abt
  val mapAccessor : Accessor.t -> (abt -> abt) -> (jdg -> jdg)
  val multiMapAccessor : Accessor.t list -> (abt -> abt) -> (jdg -> jdg)
  val variance : jdg * Accessor.t -> Variance.t

  structure View :
  sig
    val matchTrueAsEq : jdg -> (abt * abt) * abt
    val makeEqAsTrue : (abt * abt) * abt -> jdg

    datatype as_level = FINITE of RedPrlLevel.t | OMEGA

    val matchAsEqType : jdg -> (abt * abt) * as_level * RedPrlKind.t
    val makeAsEqType : (abt * abt) * as_level * RedPrlKind.t -> jdg

    datatype as_type = INTERNAL_TYPE of abt | UNIV_OMEGA of RedPrlKind.t

    val matchAsEq : jdg -> (abt * abt) * as_type
    val makeAsEq : (abt * abt) * as_type -> jdg
    val makeAsMem : abt * as_type -> jdg
    val makeAsSubType : abt * as_type -> jdg
    
    val classifier : jdg * Accessor.t -> as_type
  end
end
