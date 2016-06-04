structure UnivRules : UNIV_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ ^!
  infix 4 >>
  infix 3 |> @>

  structure LvlUtil =
  struct
    fun compareLevels (i, j) =
      let
        val RS.EXP LVL = sort i
        val RS.EXP LVL = sort j
      in
        if RedPrlAbt.eq (i, j) then
          EQUAL
        else
          let
            exception Incomparable
          in
            case (Syn.out i, Syn.out j) of
               (Syn.LSUCC i', Syn.LSUCC j') => compareLevels (i', j')
             | (Syn.LSUCC _, _) => GREATER
             | (_, Syn.LSUCC _) => LESS
             | _ => raise Incomparable
          end
          handle Incomparable =>
            raise Fail
              @@ "Levels incomparable: "
               ^ DebugShowAbt.toString i
               ^ " vs. "
               ^ DebugShowAbt.toString j
      end

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
