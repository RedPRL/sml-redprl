structure ScriptOperator : OPERATOR =
struct
  open ScriptOperatorData SortData

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
    fun arity (BIND {bindings}) =
          [ [] * [] <> TAC
          , (EXP ^ bindings) * [] <> TAC
          ] ->> TAC
      | arity MULTI =
          [ [] * [] <> VEC TAC
          ] ->> TAC
      | arity SMASH =
          [ [] * [] <> TAC
          , [] * [] <> TAC
          ] ->> TAC
      | arity (FOCUS _) =
          [ [] * [] <> TAC
          ] ->> TAC
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
      | arity REC =
          [ [] * [TAC] <> TAC
          ] ->> TAC
  end

  fun support (ELIM {target,...}) = [(target, EXP)]
    | support (HYP {target}) = [(target, EXP)]
    | support _ = []

  structure Presheaf =
  struct
    type 'i t = 'i t
    fun map f (BIND p) = BIND p
      | map f MULTI = MULTI
      | map f SMASH = SMASH
      | map f (FOCUS p) = FOCUS p
      | map f (INTRO p) = INTRO p
      | map f (ELIM {target}) =
          ELIM {target = f target}
      | map f (HYP {target}) =
          HYP {target = f target}
      | map f ID =
          ID
      | map f REC =
          REC
  end

  structure Eq =
  struct
    type 'i t = 'i t
    fun eq f (BIND p1, BIND p2) = p1 = p2
      | eq f (MULTI, MULTI) = true
      | eq f (SMASH, SMASH) = true
      | eq f (FOCUS p1, FOCUS p2) = p1 = p2
      | eq f (INTRO p1, INTRO p2) = p1 = p2
      | eq f (ELIM p1, ELIM p2) =
          f (#target p1, #target p2)
      | eq f (HYP p1, HYP p2) =
          f (#target p1, #target p2)
      | eq f (ID, ID) = true
      | eq f (REC, REC) = true
      | eq _ _ = false
  end

  structure Show =
  struct
    type 'i t = 'i t
    fun toString f (BIND _) = "bind"
      | toString f MULTI = "multi"
      | toString f SMASH = "smash"
      | toString f (FOCUS {focus,...}) = "focus{" ^ Int.toString focus ^ "}"
      | toString f (INTRO _) = "intro"
      | toString f (ELIM {target,...}) = "elim[" ^ f target ^ "]"
      | toString f (HYP {target}) = "hyp[" ^ f target ^ "]"
      | toString f ID = "id"
      | toString f REC = "rec"
  end
end
