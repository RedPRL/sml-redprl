structure RefinerKit =
struct
  structure RS = RedPrlOperator.S
  structure Syn = RedPrlAbtSyntax
  structure Ctx = SymbolTelescope and Signature = AbtSignature
  structure MetaCtx = Metavariable.Ctx and SymCtx = Symbol.Ctx and VarCtx = Variable.Ctx

  structure Lcf =
  struct
    structure Lcf = DependentLcf (Judgment)
    open Lcf

    structure HoleUtil = HoleUtil (structure Tm = RedPrlAbt and J = Judgment and T = T)

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
  type name_store = RedPrlAbt.symbol choice_sequence
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

  open RedPrlAbt Sequent
  infix $ $$ $# \
  infix 4 >>
  infix 3 |>

  (* for development *)
  exception hole
  fun ?x = raise x

  local
    exception Destruct
  in
    fun destruct m (theta : unit O.t) =
      case out m of
           theta' $ es =>
             if O.eq (fn _ => true) (O.map (fn _ => ()) theta', theta) then
               (O.support theta', es)
             else
               raise Destruct
         | _ => raise Destruct
      handle Destruct =>
        raise Fail @@ "Expected " ^ O.toString (fn _ => "-") theta
  end

  structure HoleUtil = HoleUtil (structure Tm = RedPrlAbt and J = Judgment and T = T)

  fun goalHypCtx (H >> _) = H
    | goalHypCtx (G |> jdg) = goalHypCtx jdg

  fun makeGoal jdg =
    let
      val x = newMeta ""
      val vl = Judgment.evidenceValence jdg
      val (_, tau) = vl
      val H = goalHypCtx jdg
      fun h us ms = check (x $# (us, ms), tau)
    in
      ((x,jdg), h, H)
    end

  local
    open SortData
    fun getAtomicSort m =
      case sort m of
         RedPrlOperator.S.EXP tau => tau
       | _ => raise Match
  in

    fun makeEqSequent H args =
      H >> EQ_MEM args

    fun makeMemberSequent H (m, a) =
      H >> TRUE (Syn.into (Syn.MEMBER (getAtomicSort m, m, a)), EXP)

    fun makeLevelSequent (H : Sequent.context) =
      let
        val H' = updateHyps (fn _ => Ctx.empty) H
      in
        H' >> TRUE (Syn.into (Syn.BASE LVL), LVL)
      end

    fun makeEvidence G (H : context) m =
      let
        val (xs, taus) = ListPair.unzip G
      in
        checkb
          (([], xs) \ m,
           (([], taus), sort m))
      end

  end

  fun @> (t,(x,y)) = T.snoc t x y
end
