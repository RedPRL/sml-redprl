structure UnivRules : UNIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix $ \ ^! @@
  infix 4 >>
  infix 3 |> @>

  structure LvlUtil =
  struct
    fun destLevel i =
      case infer i of
           (view, LVL) => view
         | _ =>
           raise Fail
             @@ "Expected level expression, but got "
              ^ DebugShowAbt.toString i

    fun destLSucc i =
      case destLevel i of
           LVL_OP LSUCC $ [_ \ i] => i
         | _ =>
           raise Fail
             @@ "Expected LSUCC, but got "
              ^ DebugShowAbt.toString i

    fun compareLevels (i, j) =
      let
        val i' = destLevel i
        val j' = destLevel j
      in
        if Abt.eq (i, j) then
          EQUAL
        else
          let
            exception Incomparable
          in
            case (i', j') of
                 (LVL_OP LSUCC $ [_ \ i''], LVL_OP LSUCC $ [_ \ j'']) =>
                   compareLevels (i'', j'')
               | (LVL_OP LSUCC $ [_ \ i''], _) =>
                   GREATER
               | (_, LVL_OP LSUCC $ [_ \ i'']) =>
                   LESS
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

  fun IsType alpha (G |> H >> TYPE (ty, EXP)) =
    let
      val (tau, lvl) = destUniv ty
      val lvl' = check (metactx lvl) (LVL_OP LSUCC $ [([],[]) \ lvl], LVL)
    in
      (T.empty, fn rho =>
        makeEvidence G H lvl')
    end
    | IsType _ _ = raise Match

  fun Eq alpha (G |> H >> EQ_MEM (m, n, a)) =
    let
      val ((tau1, i), (tau2, j), (tau3, k)) = (destUniv m, destUniv n, destUniv a)
      val () = if tau3 = EXP then () else raise Fail "Sort mismatch"
      val () = if tau1 = tau2 then () else raise Fail "Sort mismatch"
      val () = LvlUtil.assertLevelEq (i, j)
      val () = LvlUtil.assertLevelLt (i, k)
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | Eq _ _ = raise Match

  fun Cum alpha (G |> H >> EQ_MEM (m, n, a)) =
    let
      val (tau, i) = destUniv a
      val j = LvlUtil.destLSucc i
      val univ =
        check
          (metactx a)
          (CTT (UNIV EXP) $ [([],[]) \ j],
           tau)

      val (goal, _, _) =
        makeGoal @@
          [] |> makeEqSequent H (m, n, univ)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | Cum _ _ = raise Match

end
