structure UnivRules : UNIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix $ \ ^! @@ >>

  fun destEq m =
    case out m of
         CTT (EQ EXP) $ [_ \ m, _ \ n, _ \ a] => (m,n,a)
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

  fun Eq alpha (H >> P) =
    let
      val (m, n, a) = destEq P
      val (i, j, k) = (destUniv m, destUniv n, destUniv a)
      val () = assertLevelEq (i, j)
      val () = assertLevelLt (i, k)
    in
      (T.empty, fn rho =>
        abtToAbs (check' (CTT AX $ [], EXP)))
    end
end
