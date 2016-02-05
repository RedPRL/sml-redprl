structure NominalLcfOperator : OPERATOR =
struct
  open NominalLcfOperatorData SortData

  structure Arity = Arity

  type 'i t = 'i script_operator

  local
    fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun op<> (a, b) = (a, b) (* valence *)
    fun op->> (a, b) = (a, b) (* arity *)
    fun op^ (x, n) = List.tabulate (n, fn _ => x)
    infix 5 <> ->>
    infix 6 * ^
  in
    fun arity (SEQ n) =
          [ [] * [] <> TAC
          , (EXP ^ n) * [] <> MTAC
          ] ->> TAC
      | arity ALL =
          [ [] * [] <> TAC
          ] ->> MTAC
      | arity EACH =
          [ [] * [] <> VEC TAC
          ] ->> MTAC
      | arity (FOCUS i) =
          [ [] * [] <> TAC
          ] ->> MTAC
      | arity (INTRO _) =
          [[] * [] <> OPT EXP]
            ->> TAC
      | arity (ELIM _) =
          [[] * [] <> OPT EXP]
            ->> TAC
      | arity (HYP _) =
          [] ->> TAC
      | arity ID =
          [] ->> TAC
      | arity FAIL =
          [] ->> TAC
      | arity (TRACE tau) =
          [ [] * [] <> tau
          ] ->> TAC
      | arity REC =
          [ [] * [TAC] <> TAC
          ] ->> TAC
      | arity (CSTEP _) =
          [] ->> TAC
      | arity CSYM =
          [] ->> TAC
      | arity CEVAL =
          [] ->> TAC
  end

  fun support (ELIM {target,...}) = [(target, EXP)]
    | support (HYP {target}) = [(target, EXP)]
    | support _ = []

  fun map f =
    fn SEQ n => SEQ n
     | ALL => ALL
     | EACH => EACH
     | FOCUS i => FOCUS i
     | INTRO p => INTRO p
     | ELIM {target} => ELIM {target = f target}
     | HYP {target} => HYP {target = f target}
     | ID => ID
     | FAIL => FAIL
     | TRACE tau => TRACE tau
     | REC => REC
     | CSTEP i => CSTEP i
     | CSYM => CSYM
     | CEVAL => CEVAL

  fun eq f =
    fn (SEQ n1, SEQ n2) => n1 = n2
     | (ALL, ALL) => true
     | (EACH, EACH) => true
     | (FOCUS i1, FOCUS i2) => i1 = i2
     | (ELIM p1, ELIM p2) => f (#target p1, #target p2)
     | (HYP p1, HYP p2) => f (#target p1, #target p2)
     | (ID, ID) => true
     | (FAIL, FAIL) => true
     | (TRACE tau1, TRACE tau2) => tau1 = tau2
     | (REC, REC) => true
     | (CSTEP n1, CSTEP n2) => n1 = n2
     | (CSYM, CSYM) => true
     | (CEVAL, CEVAL) => true
     | _ => false

  fun toString f =
    fn (SEQ _) => "seq"
     | ALL => "all"
     | EACH => "each"
     | FOCUS i => "some{" ^ Int.toString i ^ "}"
     | INTRO _ => "intro"
     | ELIM {target} => "elim[" ^ f target ^ "]"
     | HYP {target} => "hyp[" ^ f target ^ "]"
     | ID => "id"
     | FAIL => "fail"
     | TRACE tau => "trace{" ^ Sort.toString tau ^ "}"
     | REC => "rec"
     | CSTEP n => "cstep{" ^ Int.toString n ^ "}"
     | CSYM => "csym"
     | CEVAL => "ceval"
end
