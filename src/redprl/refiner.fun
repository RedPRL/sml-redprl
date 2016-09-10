functor Refiner (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  infixr @@
  infix 1 |>
  infix 2 >> >: $$ // \

  structure CEquiv =
  struct
    fun EvalGoal sign _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
        val (goal, _) = makeGoal @@ H >> CJ.CEQUIV (Machine.eval sign m, Machine.eval sign n)
        val psi = T.empty >: goal
      in
        (psi, fn rho => T.lookup rho @@ #1 goal)
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]

    fun Refl _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
      in
        if Abt.eq (m, n) then
          (T.empty, fn _ => Abt.abtToAbs @@ Syn.into Syn.AX)
        else
          raise E.error [E.% "Expected", E.! m, E.% "to be alpha-equivalent to", E.! n]
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]
  end

  structure Bool =
  struct
    fun Type _ jdg =
      let
        val H >> CJ.TYPE a = jdg
        val Syn.BOOL = Syn.out a
      in
        (T.empty, fn rho =>
          Abt.abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]
  end

  structure DFun =
  struct
    fun Type alpha jdg =
      let
        val H >> CJ.TYPE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val bz = substVar (Syn.into @@ Syn.VAR (z, O.EXP), x) bx

        val (goal1, _) = makeGoal @@ H >> CJ.TYPE a
        val (goal2, _) = makeGoal @@ Hyps.snoc H z (CJ.TRUE a) >> CJ.TYPE bz
        val psi = T.empty >: goal1 >: goal2
      in
        (psi, fn rho =>
          Abt.abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected dfun typehood sequent"]

    fun True alpha jdg =
      let
        val H >> CJ.TRUE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val bz = substVar (Syn.into @@ Syn.VAR (z, O.EXP), x) bx

        val (tyGoal, _) = makeGoal @@ H >> CJ.TYPE a
        val (goal, _) = makeGoal @@ ([],[(z, O.EXP)]) |> Hyps.snoc H z (CJ.TRUE a) >> CJ.TRUE bz
        val psi = T.empty >: goal >: tyGoal
      in
        (psi, fn rho =>
           let
             val (_, [x]) \ mx = outb @@ T.lookup rho (#1 goal)
           in
             abtToAbs o Syn.into @@ Syn.LAM (x, mx)
           end)
      end
      handle Bind =>
        raise E.error [E.% "Expected dfun truth sequent"]
  end

  structure Generic =
  struct
    fun Intro alpha jdg =
      let
        val (U, G) |> jdg' = jdg
        val (goal, _) = makeGoal jdg'
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
           let
             val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb @@ T.lookup rho (#1 goal)
             val (us', sigmas') = ListPair.unzip U
             val (xs', taus') = ListPair.unzip G
           in
             checkb ((us' @ us, xs' @ xs) \ m, ((sigmas' @ sigmas, taus' @ taus), tau))
           end)
      end
      handle Bind =>
        raise E.error [E.% "Expected generic judgment"]
  end

  structure Hyp =
  struct
    fun Project z alpha jdg =
      let
        val H >> catjdg = jdg
        val catjdg' = Option.valOf (Hyps.find H z) handle _ => raise E.error [E.% @@ "No such hypothesis " ^ Sym.toString z ^ "in context"]
      in
        if CJ.eq (catjdg, catjdg') then
          (T.empty, fn rho =>
            abtToAbs o Syn.into @@ Syn.VAR (z, CJ.synthesis catjdg))
        else
          raise E.error [E.% "Hypothesis does not match goal"]
      end
      handle Bind =>
        raise E.error [E.% "Expected sequent judgment"]
  end

  structure Truth =
  struct
    fun Witness tm alpha jdg =
      let
        val H >> CJ.TRUE ty = jdg
        val (goal, _) = makeGoal @@ H >> CJ.MEM (tm, ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
          abtToAbs tm)
      end
      handle Bind =>
        raise E.error [E.% "Expected truth sequent"]
  end

  structure Membership =
  struct
    fun Intro alpha jdg =
      let
        val H >> CJ.MEM (tm, ty) = jdg
        val (goal, _) = makeGoal @@ H >> CJ.EQ ((tm, tm), ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
          abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected member sequent"]
  end

  structure Equality =
  struct
    fun Hyp alpha jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = if Var.eq (x, y) then () else raise E.error [E.% "Equality.Hyp: variable mismatch"]
        val catjdg = Option.valOf (Hyps.find H x) handle _ => raise E.error [E.% "Equality.Hyp: cannot find hypothesis"]
        val ty' =
          case catjdg of
             CJ.TRUE ty => ty
           | _ => raise E.error [E.% "Equality.Hyp: expected truth hypothesis"]
      in
        if Syn.Tm.eq (ty, ty') then
          (T.empty, fn rho => abtToAbs @@ Syn.into Syn.AX)
        else
          raise E.error [E.% @@ "Expected type of hypothesis " ^ Var.toString x ^ " to be", E.! ty, E.% "but found", E.! ty']
      end
      handle Bind =>
        raise E.error [E.% "Expected variable-equality sequent"]
  end

  local
    open Tacticals infix ORELSE

    fun matchGoal f alpha jdg =
      f jdg alpha jdg

    fun StepTrue sign ty =
      case Syn.out ty of
         Syn.DFUN _ => DFun.True
       | _ => raise E.error [E.% "Could not find introduction rule for", E.! ty]

    fun StepType sign ty =
      case Syn.out ty of
         Syn.BOOL => Bool.Type
       | Syn.DFUN _ => DFun.Type
       | _ => raise E.error [E.% "Could not find typehood rule for", E.! ty]

    fun StepEq sign ((m, n), ty) =
      case Syn.out m of
         Syn.VAR _ => Equality.Hyp
       | _ => raise E.error [E.% "Could not find suitable equality rule for", E.! m, E.% "and", E.! n, E.% "at type", E.! ty]

    fun StepJdg sign = matchGoal
      (fn _ |> _ => Generic.Intro
        | _ >> CJ.TRUE ty => StepTrue sign ty
        | _ >> CJ.TYPE ty => StepType sign ty
        | _ >> CJ.MEM _ => Membership.Intro
        | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
        | jdg => raise E.error [E.% ("Could not find suitable rule for " ^ Seq.toString CJ.toString jdg)])
  in
    val Auto = StepJdg
  end
end
