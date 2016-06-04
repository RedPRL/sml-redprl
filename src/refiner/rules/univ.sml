structure UnivRules : UNIV_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ ^!
  infix 4 >>
  infix 3 |> @>

  structure LvlUtil =
  struct
    datatype view = @+ of RedPrlAbt.abt * int
    infix @+
    exception Incomparable

    fun compareView (b1 @+ k1, b2 @+ k2) =
      if RedPrlAbt.eq (b1, b2) then
        Int.compare (k1, k2)
      else
        raise Incomparable

    fun lsucc (b @+ k) =
      b @+ k + 1

    fun viewLevel lvl =
      let
        val RS.EXP LVL = sort lvl
      in
        case Syn.outOpen lvl of
           Syn.APP (Syn.LSUCC lvl') => lsucc @@ viewLevel lvl'
         | _ => lvl @+ 0
      end

    fun compareLevels (i, j) =
      compareView (viewLevel i, viewLevel j)

    fun assertLevelEq (i, j) =
      case compareLevels (i, j) of
           EQUAL => ()
         | _ =>
             raise Fail
               @@ "Expected "
                ^ DebugShowAbt.toString i
                ^ " == "
                ^ DebugShowAbt.toString j

    fun assertLevelLt (i, j) =
      case compareLevels (i, j) of
           LESS => ()
         | _ =>
             raise Fail
               @@ "Expected "
                ^ DebugShowAbt.toString i
                ^ " < "
                ^ DebugShowAbt.toString j

  end

  fun IsType alpha (H >> TYPE (ty, EXP)) =
    let
      val Syn.UNIV (tau, lvl) = Syn.out ty
      val lvl' = Syn.into @@ Syn.LSUCC lvl
    in
      (T.empty, fn rho =>
        abtToAbs lvl')
    end
    | IsType _ _ = raise Match

  fun Eq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val (Syn.UNIV (tau1, i), Syn.UNIV (tau2, j), Syn.UNIV (tau3, k)) = (Syn.out m, Syn.out n, Syn.out a)
      val () = if tau3 = EXP then () else raise Fail "Sort mismatch"
      val () = if tau1 = tau2 then () else raise Fail "Sort mismatch"
      val () = LvlUtil.assertLevelEq (i, j)
      val () = LvlUtil.assertLevelLt (i, k)
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | Eq _ _ = raise Match

  fun Cum alpha (H >> EQ_MEM (m, n, a)) =
    let
      val Syn.UNIV (tau, i) = Syn.out a
      val Syn.LSUCC j = Syn.out i
      val univ = Syn.into @@ Syn.UNIV (EXP, j)

      val (goal, _, _) =
        makeGoal @@
          makeEqSequent H (m, n, univ)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | Cum _ _ = raise Match

end
