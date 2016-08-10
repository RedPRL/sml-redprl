structure NominalLcfOperators =
struct
  (* We use symbols/atoms to index into the context. *)

  structure Sort = RedPrlAtomicSort

  datatype 'i script_operator =
      SEQ of Sort.t list
    | ORELSE
    | ALL | EACH | FOCUS of int
    | PROGRESS
    | REC
    | INTRO of int option
    | EQ of int option
    | CHKINF
    | EXT
    | ETA of 'i * Sort.t
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

structure NominalLcfV : JSON_ABT_OPERATOR =
struct
  open NominalLcfOperators SortData

  structure Ar = RedPrlAtomicArity
  type 'i t = 'i script_operator

  open ArityNotation
  infix 5 <> ->>
  infix 6 *

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
    | arity CHKINF =
        [] ->> TAC
    | arity EXT =
        [] ->> TAC
    | arity CUM =
        [] ->> TAC
    | arity (ELIM _) =
        [] ->> TAC
    | arity (ETA _) =
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

  fun support (ELIM (target, tau)) = [(target, tau)]
    | support (ETA (target, tau)) = [(target, tau)]
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
     | CHKINF => CHKINF
     | CUM => CUM
     | ELIM (target, tau) => ELIM (f target, tau)
     | ETA (target, tau) => ETA (f target, tau)
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
     | INTRO rule => "intro" ^ (case rule of NONE => "" | SOME i => "{" ^ Int.toString i ^ "}")
     | EQ rule => "eq" ^ (case rule of NONE => "" | SOME i => "{" ^ Int.toString i ^ "}")
     | EXT => "ext"
     | CHKINF => "chk-inf"
     | CUM => "cum"
     | ELIM (target,tau) => "elim[" ^ f target ^ " : " ^ Sort.toString tau ^ "]"
     | ETA (target,tau) => "eta[" ^ f target ^ " : " ^ Sort.toString tau ^ "]"
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

  structure J = Json and S = RedPrlAtomicSortJson


  fun encodeOpt f =
    fn SOME x => f x
     | NONE => J.Null

  fun decodeOpt f =
    fn J.Null => NONE
     | m => Option.map SOME (f m)

  fun encode f =
    fn SEQ taus => J.Obj [("seq", J.Array (List.map S.encode taus))]
     | ORELSE => J.String "orelse"
     | ALL => J.String "all"
     | EACH => J.String "each"
     | FOCUS i => J.Obj [("focus", J.Int i)]
     | PROGRESS => J.String "progress"
     | REC => J.String "rec"
     | INTRO i => J.Obj [("intro", encodeOpt J.Int i)]
     | EQ i => J.Obj [("eq", encodeOpt J.Int i)]
     | CHKINF => J.String "chkinf"
     | CUM => J.String "cum"
     | EXT => J.String "ext"
     | ETA (a, tau) => J.Obj [("eta", J.Array [f a, S.encode tau])]
     | ELIM (a, tau) => J.Obj [("elim", J.Array [f a, S.encode tau])]
     | HYP (a, tau) => J.Obj [("hyp", J.Array [f a, S.encode tau])]
     | UNHIDE (a, tau) => J.Obj [("unhide", J.Array [f a, S.encode tau])]
     | AUTO => J.String "auto"
     | ID => J.String "id"
     | FAIL => J.String "fail"
     | TRACE tau => J.Obj [("trace", S.encode tau)]
     | CSTEP i => J.Obj [("cstep", J.Int i)]
     | CEVAL => J.String "ceval"
     | CSYM => J.String "csym"
     | REWRITE_GOAL tau => J.Obj [("rewrite_goal", S.encode tau)]
     | EVAL_GOAL a => J.Obj [("eval_goal", encodeOpt f a)]
     | NORMALIZE a => J.Obj [("normalize", encodeOpt f a)]
     | WITNESS tau => J.Obj [("witness", S.encode tau)]
     | UNFOLD (a, b) => J.Obj [("unfold", J.Array [f a, encodeOpt f b])]
     | HYP_VAR a => J.Obj [("hyp_var", f a)]

  open OptionUtil
  infix **

  val decodeInt =
    fn J.Int i => SOME i
     | _ => NONE


  fun decode f =
    fn J.Obj [("seq", J.Array taus)] => Option.map SEQ (traverseOpt S.decode taus)
     | J.String "orelse" => SOME ORELSE
     | J.String "all" => SOME ALL
     | J.String "each" => SOME EACH
     | J.Obj [("focus", J.Int i)] => SOME (FOCUS i)
     | J.String "progress" => SOME PROGRESS
     | J.String "rec" => SOME REC
     | J.Obj [("intro", i)] => Option.map INTRO (decodeOpt decodeInt i)
     | J.Obj [("eq", i)] => Option.map EQ (decodeOpt decodeInt i)
     | J.String "chkinf" => SOME CHKINF
     | J.String "cum" => SOME CUM
     | J.String "ext" => SOME EXT
     | J.Obj [("eta", J.Array [a, tau])] => Option.map ETA (f a ** S.decode tau)
     | J.Obj [("elim", J.Array [a, tau])] => Option.map ELIM (f a ** S.decode tau)
     | J.Obj [("hyp", J.Array [a, tau])] => Option.map HYP (f a ** S.decode tau)
     | J.Obj [("unhide", J.Array [a, tau])] => Option.map UNHIDE (f a ** S.decode tau)
     | J.String "auto" => SOME AUTO
     | J.String "id" => SOME ID
     | J.String "fail" => SOME FAIL
     | J.Obj [("trace", tau)] => Option.map TRACE (S.decode tau)
     | J.Obj [("cstep", J.Int i)] => SOME (CSTEP i)
     | J.String "ceval" => SOME CEVAL
     | J.String "csym" => SOME CSYM
     | J.Obj [("rewrite_goal", tau)] => Option.map REWRITE_GOAL (S.decode tau)
     | J.Obj [("eval_goal", a)] => Option.map EVAL_GOAL (decodeOpt f a)
     | J.Obj [("normalize", a)] => Option.map NORMALIZE (decodeOpt f a)
     | J.Obj [("witness", tau)] => Option.map WITNESS (S.decode tau)
     | J.Obj [("unfold", J.Array [a, b])] => Option.map UNFOLD (f a ** decodeOpt f b)
     | J.Obj [("hyp_var", a)] => Option.map HYP_VAR (f a)
     | _ => NONE
end
