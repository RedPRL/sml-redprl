structure NominalLcfOperatorData =
struct
  (* We use symbols/atoms to index into the context. *)

  type intro_params =
    {rule : int option}

  type eq_params =
    {rule : int option}

  datatype 'i script_operator =
      SEQ of Sort.t list
    | ORELSE
    | ALL | EACH | FOCUS of int
    | PROGRESS
    | REC
    | INTRO of intro_params
    | EQ of eq_params
    | EXT
    | CUM
    | ELIM of 'i * Sort.t | HYP of 'i * Sort.t | UNHIDE of 'i * Sort.t
    | AUTO
    | ID | FAIL | TRACE of Sort.t
    | CSTEP of int | CEVAL | CSYM
    | REWRITE_GOAL of Sort.t | EVAL_GOAL of 'i option | NORMALIZE of 'i option
    | WITNESS of Sort.t
    | UNFOLD of 'i * 'i option
    | HYP_VAR of 'i
end

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
    fun arity (SEQ sorts) =
          [ [] * [] <> MTAC
          , sorts * [] <> TAC
          ] ->> TAC
      | arity ORELSE =
          [ [] * [] <> TAC
          , [] * [] <> TAC
          ] ->> TAC
      | arity PROGRESS =
          [ [] * [] <> TAC
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
          [] ->> TAC
      | arity (EQ _) =
          [] ->> TAC
      | arity EXT =
          [] ->> TAC
      | arity CUM =
          [] ->> TAC
      | arity (ELIM _) =
          [] ->> TAC
      | arity (HYP _) =
          [] ->> TAC
      | arity (UNHIDE _) =
          [] ->> TAC
      | arity AUTO =
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
      | arity (REWRITE_GOAL tau) =
          [ [] * [] <> tau
          ] ->> TAC
      | arity (EVAL_GOAL _) =
          [] ->> TAC
      | arity (WITNESS tau) =
          [ [] * [] <> tau
          ] ->> TAC
      | arity (UNFOLD _) =
          [] ->> TAC
      | arity (NORMALIZE _) =
          [] ->> TAC

      | arity (HYP_VAR _) =
          [] ->> EXP
  end

  fun support (ELIM (target, tau)) = [(target, tau)]
    | support (HYP (target, tau)) = [(target, tau)]
    | support (UNHIDE (target, tau)) = [(target, tau)]
    | support (UNFOLD (i, oj)) =
        [(i, SortData.OPID)] @
          (case oj of
               SOME i => [(i, SortData.EXP)]
             | NONE => [])
    | support (NORMALIZE oi) =
        (case oi of
             SOME i => [(i, SortData.EXP)] (* TODO: sort *)
           | NONE => [])
    | support (HYP_VAR i) = [(i, SortData.EXP)]
    | support _ = []

  fun map f =
    fn SEQ sorts => SEQ sorts
     | ORELSE => ORELSE
     | PROGRESS => PROGRESS
     | ALL => ALL
     | EACH => EACH
     | FOCUS i => FOCUS i
     | INTRO p => INTRO p
     | EQ p => EQ p
     | EXT => EXT
     | CUM => CUM
     | ELIM (target, tau) => ELIM (f target, tau)
     | HYP (target, tau) => HYP (f target, tau)
     | UNHIDE (target, tau) => UNHIDE (f target, tau)
     | AUTO => AUTO
     | ID => ID
     | FAIL => FAIL
     | TRACE tau => TRACE tau
     | REC => REC
     | CSTEP i => CSTEP i
     | CSYM => CSYM
     | CEVAL => CEVAL
     | REWRITE_GOAL tau => REWRITE_GOAL tau
     | WITNESS tau => WITNESS tau
     | EVAL_GOAL oi => EVAL_GOAL (Option.map f oi)
     | UNFOLD (i, oj) => UNFOLD (f i, Option.map f oj)
     | NORMALIZE oi => NORMALIZE (Option.map f oi)
     | HYP_VAR i => HYP_VAR (f i)

  fun eq f =
    fn (SEQ sorts1, SEQ sorts2) => sorts1 = sorts2
     | (ORELSE, ORELSE) => true
     | (ALL, ALL) => true
     | (EACH, EACH) => true
     | (FOCUS i1, FOCUS i2) => i1 = i2
     | (ELIM (u, sigma), ELIM (v, tau)) => f (u, v) andalso sigma = tau
     | (HYP (u, sigma), HYP (v, tau)) => f (u, v) andalso sigma = tau
     | (UNHIDE (u, sigma), UNHIDE (v, tau)) => f (u, v) andalso sigma = tau
     | (AUTO, AUTO) => true
     | (ID, ID) => true
     | (FAIL, FAIL) => true
     | (TRACE tau1, TRACE tau2) => tau1 = tau2
     | (REC, REC) => true
     | (CSTEP n1, CSTEP n2) => n1 = n2
     | (CSYM, CSYM) => true
     | (CEVAL, CEVAL) => true
     | (REWRITE_GOAL tau1, REWRITE_GOAL tau2) => tau1 = tau2
     | (WITNESS tau1, WITNESS tau2) => tau1 = tau2
     | (EVAL_GOAL oi, EVAL_GOAL oj) =>
         (case (oi, oj) of
             (SOME i, SOME j) => f (i, j)
           | (NONE, NONE) => true
           | _ => false)
     | (UNFOLD (i1, oj1), UNFOLD (i2, oj2)) =>
         f (i1, i2) andalso
           (case (oj1, oj2) of
               (SOME j1, SOME j2) => f (j1, j2)
             | (NONE, NONE) => true
             | _ => false)
     | (NORMALIZE oi, NORMALIZE oj) =>
         (case (oi, oj) of
             (SOME i, SOME j) => f (i, j)
           | (NONE, NONE) => true
           | _ => false)
     | (HYP_VAR i, HYP_VAR j) => f (i, j)
     | _ => false

  fun toString f =
    fn (SEQ _) => "seq"
     | ORELSE => "orelse"
     | PROGRESS => "progress"
     | ALL => "all"
     | EACH => "each"
     | FOCUS i => "some{" ^ Int.toString i ^ "}"
     | INTRO {rule} => "intro" ^ (case rule of NONE => "" | SOME i => "{" ^ Int.toString i ^ "}")
     | EQ {rule} => "eq" ^ (case rule of NONE => "" | SOME i => "{" ^ Int.toString i ^ "}")
     | EXT => "ext"
     | CUM => "cum"
     | ELIM (target,tau) => "elim[" ^ f target ^ " : " ^ Sort.toString tau ^ "]"
     | HYP (target, tau) => "hyp[" ^ f target ^ " : " ^ Sort.toString tau ^ "]"
     | UNHIDE (target, tau) => "unhide[" ^ f target ^ " : " ^ Sort.toString tau ^ "]"
     | AUTO => "auto"
     | ID => "id"
     | FAIL => "fail"
     | TRACE tau => "trace{" ^ Sort.toString tau ^ "}"
     | REC => "rec"
     | CSTEP n => "cstep{" ^ Int.toString n ^ "}"
     | CSYM => "csym"
     | CEVAL => "ceval"
     | REWRITE_GOAL tau => "rewrite-goal{" ^ Sort.toString tau ^ "}"
     | EVAL_GOAL oi => "eval-goal" ^ (case oi of NONE => "" | SOME i => " in " ^ f i)
     | WITNESS tau => "witness{" ^ Sort.toString tau ^ "}"
     | UNFOLD (i, oj) => "unfold[" ^ f i ^ "]" ^ (case oj of NONE => "" | SOME j => " in " ^ f j)
     | NORMALIZE oi => "normalize" ^ (case oi of NONE => "" | SOME i => " in " ^ f i)
     | HYP_VAR i => "@" ^ f i
end

