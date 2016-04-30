structure RefinerKit =
struct
  structure Ctx = SymbolTelescope and Signature = AbtSignature
  structure Lcf =
  struct
    structure Lcf = DependentLcf (Judgment)
    open Lcf

    structure HoleUtil = HoleUtil (structure Tm = Abt and J = Judgment and T = T)

    fun stateToString (psi, vld) =
      let
        open T.ConsView
        fun go i =
          fn EMPTY => (T.empty, "")
           | CONS (x, jdg, tl) =>
               let
                 val var = Metavariable.named ("?" ^ Int.toString i)
                 val goal = "\nHOLE " ^ Metavariable.toString var ^ "\n--------------------------------------------\n" ^ Judgment.judgmentToString jdg
                 val vartm = HoleUtil.makeHole (var, Judgment.evidenceValence jdg)
                 val tl' = T.map (Judgment.substEvidence (vartm, x)) tl
                 val (rho, rest) = go (i + 1) (out tl')
               in
                 (T.snoc rho x vartm, goal ^ "\n" ^ rest)
               end

        val (env, subgoals) = go 0 (out psi)
        val preamble = Judgment.evidenceToString (vld env)
      in
        "WITNESS:\n============================================\n\n" ^ preamble ^ "\n\n" ^ subgoals
      end
  end

  structure Telescope = Lcf.T and T = Lcf.T
  structure Tacticals = Tacticals(Lcf)

  type 'a choice_sequence = int -> 'a
  type name_store = Abt.symbol choice_sequence
  type ntactic = name_store -> Tacticals.Lcf.tactic
  type nmultitactic = name_store -> Tacticals.Lcf.multitactic

  local
    val counter = ref 0
  in
    fun newMeta str =
      let
        val i = !counter
      in
        counter := i + 1;
        Metavariable.named ("?" ^ str ^ Int.toString i)
      end
  end


  fun @@ (f,x) = f x
  infix 0 @@

  open Abt Sequent
  infix $ $# \
  infix 4 >>
  infix 3 |>

  (* for development *)
  exception hole
  fun ?x = raise x

  local
    exception Destruct
  in
    fun destruct m (theta : unit Operator.t) =
      case out m of
           theta' $ es =>
             if Operator.eq (fn _ => true) (Operator.map (fn _ => ()) theta', theta) then
               (Operator.support theta', es)
             else
               raise Destruct
         | _ => raise Destruct
      handle Destruct =>
        raise Fail @@ "Expected " ^ Operator.toString (fn _ => "-") theta
  end

  structure HoleUtil = HoleUtil (structure Tm = Abt and J = Judgment and T = T)

  fun makeGoal (jdg as G |> H >> _) =
    let
      val x = newMeta ""
      val vl = Judgment.evidenceValence jdg
      val (_, tau) = vl
      val mctx = MetaCtx.insert (getMetas H) x vl
      fun h us ms = check mctx (x $# (us, ms), tau)
      val H' = updateMetas (fn _ => mctx) H
    in
      ((x,jdg), h, H)
    end

  local
    open OperatorData CttOperatorData SortData
  in
    fun destVar m =
      case out m of
           `x => x
         | _ => raise Fail @@ "Expected variable, but got " ^ DebugShowAbt.toString m


    fun destAx m =
      case out m of
           CTT AX $ _ => ()
         | _ => raise Fail @@ "Expected Ax, but got " ^ DebugShowAbt.toString m

    fun destEq m =
      case out m of
           CTT (EQ tau) $ [_ \ m, _ \ n, _ \ a] => (tau, m,n,a)
         | _ => raise Fail @@ "Expected equality type, but got " ^ DebugShowAbt.toString m

    fun destUniv m =
      case out m of
           CTT (UNIV tau) $ [_ \ i] => (tau, i)
         | _ => raise Fail @@ "Expected universe, but got " ^ DebugShowAbt.toString m

    fun destCEquiv P =
      case (out P) of
           CTT (CEQUIV tau) $ [_ \ m, _ \ n] =>
             let
               val tau1 = sort m
               val tau2 = sort n
               val () =
                 if tau1 = tau2 andalso tau = tau1 then
                   ()
                 else
                   raise Fail "Incompatible sorts in CEquiv"
             in
               (tau, m, n)
             end
         | _ => raise Fail "Expected CEquiv"

    fun makeEq mctx (m,n,a) =
      check
        mctx
        (CTT (EQ (sort m)) $ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a],
         EXP)

    fun makeCEquiv mctx (m,n) =
      check
        mctx
        (CTT (CEQUIV (sort m)) $ [([],[]) \ m, ([],[]) \ n],
         EXP)

    fun makeMember mctx (m,a) =
      check
        mctx
        (CTT (MEMBER (sort m)) $ [([],[]) \ m, ([],[]) \ a],
         EXP)

    fun makeSquash mctx tau a =
      check
        mctx
        (CTT (SQUASH tau) $ [([],[]) \ a],
         EXP)

    fun makeUniv lvl =
      check
        (metactx lvl)
        (CTT (UNIV EXP) $ [([],[]) \ lvl],
         EXP)

    fun makeEqSequent H args =
      H >> EQ_MEM args

    fun makeMemberSequent H args =
      H >> TRUE (makeMember (getMetas H) args, EXP)

    fun makeLevelSequent (H : Sequent.context) =
      let
        val H' = updateHyps (fn _ => Ctx.empty) H
      in
        H' >> TRUE (check' (CTT (BASE LVL) $ [], EXP), LVL)
      end

    val makeAx = check' (CTT AX $ [], EXP)

    fun makeEvidence G (H : context) m =
      let
        val (xs, taus) = ListPair.unzip G
      in
        checkb
          (getMetas H)
          (([], xs) \ m,
           (([], taus), sort m))
      end

  end

  fun @> (t,(x,y)) = T.snoc t x y
end
