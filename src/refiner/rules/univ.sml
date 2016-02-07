structure UnivRules : UNIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix $ \ ^! @@ >>

  fun destLevel i =
    case infer i of
         (view, LVL) => view
       | _ =>
           raise Fail
             @@ "Expected level expression, but got "
              ^ DebugShowAbt.toString i

  (* Find the basis of a level hierarchy *)
  fun levelGetBase i =
    case destLevel i of
         LVL_OP LSUCC $ [_ \ i] =>
           levelGetBase i
       | _ => i

  fun compareLevels (i, j) =
    let
      val i' = destLevel i
      val j' = destLevel j
    in
      if Abt.eq (i, j) then
        EQUAL
      else
        let
          val b1 = levelGetBase i
          val b2 = levelGetBase j
          exception Incomparable
        in
          if Abt.eq (b1, b2) then
            case (i', j') of
                 (LVL_OP LSUCC $ [_ \ i''], LVL_OP LSUCC $ [_ \ j'']) =>
                   compareLevels (i'', j'')
               | (LVL_OP LSUCC $ [_ \ i''], _) =>
                   GREATER
               | (_, LVL_OP LSUCC $ [_ \ i'']) =>
                   LESS
               | _ => raise Incomparable
          else
            raise Incomparable
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

  fun Eq alpha (H >> (P, _)) =
    let
      val (tau, m, n, a) = destEq P
      val () = if tau = EXP then () else raise Fail "Expected exp"
      val ((tau1, i), (tau2, j), (tau3, k)) = (destUniv m, destUniv n, destUniv a)
      val () = if tau1 = tau2 andalso tau2 = tau3 then () else raise Fail "Sort mismatch"
      val () = assertLevelEq (i, j)
      val () = assertLevelLt (i, k)
    in
      (T.empty, fn rho =>
        abtToAbs (check' (CTT AX $ [], TRIV)))
    end
end
