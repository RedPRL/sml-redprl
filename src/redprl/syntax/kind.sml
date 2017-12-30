structure RedPrlKind =
struct
  (*
   * DISCRETE < KAN < HCOM < STABLE
   *                < COE  <
   *
   * and KAN = meet (HCOM, COE)
   *)

  (* Please keep the following invariants when adding new kinds:
   *
   * (1) All judgments should still be closed under any substitution! In
   *     particular, the property that a type A has kind K is closed under any
   *     substitution.
   * (2) If two types are related with respect to a stronger kind (like KAN),
   *     then they are related with respect to a weaker kind (like STABLE).
   *     A stronger kind might demand more things to be equal. For example,
   *     the equality between two types with respect to KAN means that they
   *     are equally Kan, while the equality with respect to STABLE only says
   *     they are equal pretypes.
   * (3) The PER associated with A should *never* depend on its kind. Kinds
   *     should be properties of (the PER of) A.
   * (4) We say KAN = meet (HCOM, COE) because if two types are equally "HCOM"
   *     and equally "COE" then they are equally Kan. Always remember to check
   *     the binary cases.
   *)
  datatype kind = DISCRETE | KAN | HCOM | COE | STABLE
  type t = kind

  val COM = KAN

  val toString =
    fn DISCRETE => "discrete"
     | KAN => "kan"
     | HCOM => "hcom"
     | COE => "coe"
     | STABLE => "stable"

  local
    structure Internal :
    (* this could be the new meet semi-lattice *)
    sig
      type t = kind

      val top : t
      val <= : t * t -> bool
      val eq : t * t -> bool
      val meet : t * t -> t

      (* residual (a, b)
       *
       * Let c be the greatest element such that `meet (b, c) <= a`.
       * The return value is SOME c if c is not top, or NONE otherwise.
       * *)
      val residual : t * t -> t option
    end
    =
    struct
      type t = kind
      val top = STABLE

      val meet =
        fn (DISCRETE, _) => DISCRETE
         | (_, DISCRETE) => DISCRETE
         | (KAN, _) => KAN
         | (_, KAN) => KAN
         | (HCOM, COE) => KAN
         | (COE, HCOM) => KAN
         | (HCOM, _) => HCOM
         | (_, HCOM) => HCOM
         | (COE, _) => COE
         | (_, COE) => COE
         | (STABLE, STABLE) => STABLE

      val residual =
        fn (_, DISCRETE) => NONE
         | (DISCRETE, _) => SOME DISCRETE
         | (_, KAN) => NONE
         | (KAN, HCOM) => SOME COE
         | (KAN, COE) => SOME HCOM
         | (KAN, _) => SOME KAN
         | (COE, HCOM) => SOME COE
         | (HCOM, COE) => SOME HCOM
         | (_, HCOM) => NONE
         | (HCOM, _) => SOME HCOM
         | (_, COE) => NONE
         | (COE, _) => SOME COE
         | (STABLE, STABLE) => NONE

      fun op <= (a, b) = residual (b, a) = NONE
      val eq = op=
    end
  in
    open Internal
  end
end