structure UnivRules : UNIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix $ \ ^! @@ >>

  fun destEq m =
    case out m of
         CTT (EQ tau) $ [_ \ m, _ \ n, _ \ a] => (tau,m,n,a)
       | _ => raise Fail @@ "Expected equality type, but got " ^ DebugShowAbt.toString m

  fun destUniv m =
    case out m of
         CTT UNIV $ [_ \ i] => i
       | _ => raise Fail @@ "Expected universe, but got " ^ DebugShowAbt.toString m


  fun destLevel i =
    case infer i of
         (view, LVL) => view
       | _ =>
           raise Fail
             @@ "Expected level expression, but got "
              ^ DebugShowAbt.toString i

  fun compareLevels (i, j) =
    let
      val i' = destLevel i
      val j' = destLevel j
    in
      if Abt.eq (i, j) then
        EQUAL
      else
        case (i', j') of
             (LVL_OP (LBASE u) $ _, LVL_OP (LBASE v) $ _) =>
               raise Fail "Levels lie in different hierarchies"
           | (LVL_OP (LBASE u) $ _, _) =>
               LESS
           | (_, LVL_OP (LBASE u) $ _) =>
               GREATER
           | (LVL_OP LSUCC $ [_ \ i''], LVL_OP LSUCC $ [_ \ j'']) =>
               compareLevels (i'', j'')
           | _ =>
               raise Fail "Levels incomparable"
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

  fun Eq alpha (H >> P) =
    let
      val (tau, m, n, a) = destEq P
      val (i, j, k) = (destUniv m, destUniv n, destUniv a)
      val () = assertLevelEq (i, j)
      val () = assertLevelLt (i, k)
    in
      (T.empty, fn rho =>
        abtToAbs (check' (CTT AX $ [], EXP)))
    end
end
