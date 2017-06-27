structure MiniSig =
struct
  structure Tm = RedPrlAbt

  type abt = Tm.abt
  type metavar = Tm.metavariable
  type ast = RedPrlAst.ast
  type sort = Tm.sort
  type psort = Tm.psort
  type valence = RedPrlArity.valence
  type symbol = Tm.symbol
  type opid = Tm.symbol
  type jdg = RedPrlJudgment.jdg

  type 'a params = ('a * psort) list
  type 'a arguments = ('a * valence) list

  type src_opid = string
  type entry =
    {sourceOpid : src_opid,
     spec : jdg,
     state : Lcf.jdg Lcf.state}

  type src_catjdg = ast RedPrlCategoricalJudgment.jdg
  type src_seqhyp = string * src_catjdg
  type src_sequent = src_seqhyp list * src_catjdg
  type src_genjdg = (string * psort) list * src_sequent
  type src_rulespec = src_genjdg list * src_sequent

  datatype src_decl =
      DEF of {arguments : string arguments, params : string params, sort : sort, definiens : ast}
    | THM of {arguments : string arguments, params : string params, goal : src_sequent, script : ast}
    | RULE of {arguments : string arguments, params : string params, spec : src_rulespec, script : ast}
    | TAC of {arguments : string arguments, params : string params, script : ast}

  datatype 'opid cmd =
      PRINT of 'opid
    | EXTRACT of 'opid

  type src_cmd = src_opid cmd

  datatype src_elt =
      DECL of string * src_decl * Pos.t
    | CMD of src_cmd * Pos.t

  (* elaborated declarations *)
  datatype elab_decl =
      EDEF of entry
    | ECMD of opid cmd

  structure Telescope = Telescope (StringAbtSymbol)
  structure ETelescope = Telescope (Tm.Sym)
  structure NameEnv = AstToAbt.NameEnv

  (* A signature / [sign] is a telescope of declarations. *)
  type src_sign = (src_decl * Pos.t option) Telescope.telescope

  (* An elaborated signature is a telescope of definitions. *)
  type elab_sign = elab_decl ElabMonad.t ETelescope.telescope

  type sign =
    {sourceSign : src_sign,
     elabSign : elab_sign,
     nameEnv : Tm.symbol NameEnv.dict}

  structure E = ElabMonadUtil (ElabMonad)
  fun lookup ({elabSign, ...} : sign) opid =
    case E.run (ETelescope.lookup elabSign opid) handle _ => raise Fail "mini" of
        SOME (EDEF defn) => defn
      | _ => raise Fail "Elaboration failed"

  fun entryParams (entry : entry) : symbol params = 
    let
      val RedPrlSequent.>> ((I, _), _) = #spec entry
    in
      I
    end

  fun entryArguments (entry : entry) : metavar arguments =
    let
      val Lcf.|> (subgoals, _) = #state entry
    in
      Lcf.Tl.foldr (fn (x, jdg, args) => (x, RedPrlJudgment.sort jdg) :: args) [] subgoals
    end

  fun entrySort (entry : entry) : sort = 
    let
      val RedPrlSequent.>> (_, jdg) = #spec entry
    in
      RedPrlCategoricalJudgment.synthesis jdg
    end

  fun unifyCustomOperator (entry : entry) (ps : Tm.param list) (es : abt Tm.bview list) : Tm.metaenv * Tm.symenv =
    let
      val params = entryParams entry
      val arguments = entryArguments entry
      val srho = ListPair.foldl (fn ((u, _), p, ctx) => Sym.Ctx.insert ctx u p) Sym.Ctx.empty (params, ps)
      val mrho = ListPair.foldl (fn ((x, vl), e, ctx) => Metavar.Ctx.insert ctx x (Tm.checkb (e, vl))) Metavar.Ctx.empty (arguments, es)
              handle _ => raise Fail "Fuck/unifyCustomOperator"

    in
      (mrho, srho)
    end

  local
    open RedPrlOpData Tm RedPrlSequent
    infix $ \ >>

    (* Observe that hypotheses have a dual nature: they are both symbols and variables. When reviving a proof state,
      we have to rename hypotheses in *both* their moments. This routine constructs the appropriate substitution
      for hypotheses qua variables. *)
    fun hypothesisRenaming (entry : entry) (ps : Tm.param list) : Tm.varenv =
      let
        fun handleHyp ((u, psort), ptm, ctx) =
          case psort of
            RedPrlSortData.HYP tau =>
              let
                val v = case ptm of RedPrlParameterTerm.VAR v => v
                           | _ => raise Fail "Hypothesis renaming failed: not a variable"
              in
                Var.Ctx.insert ctx u (Tm.check (Tm.`v, tau))
              end
          | _ => ctx
      in
        ListPair.foldl handleHyp Var.Ctx.empty (entryParams entry, ps)
      end

    fun relabelSequent (entry : entry) (ps : Tm.param list) : abt jdg -> abt jdg =
      let
        val rho =
          ListPair.foldrEq
            (fn ((u, _), P.VAR v, r) => Sym.Ctx.insert r u v
              | (_, _, r) => r)
            Sym.Ctx.empty
            (entryParams entry, ps)
      in
        RedPrlSequent.relabel rho
      end
  in
    fun resuscitateTheorem sign opid ps =
      let
        val entry = lookup sign opid
        val goal = #spec entry
        val Lcf.|> (subgoals, validation) = #state entry
        val args = Lcf.Tl.foldr (fn (x, jdg, args) => outb (Lcf.L.var x (RedPrlJudgment.sort jdg)) :: args) [] subgoals

        val (mrho, srho) = unifyCustomOperator entry ps args
        val vrho = hypothesisRenaming entry ps
        val reviveTerm = substVarenv vrho o substSymenv srho o substMetaenv mrho
        val reviveSequent = relabelSequent entry ps o RedPrlSequent.map reviveTerm

        fun mapEff f = Lcf.Eff.bind (Lcf.Eff.ret o f)
        val subgoals' = Lcf.Tl.map (mapEff reviveSequent) subgoals
        val validation' = mapAbs reviveTerm validation
        val goal' = reviveSequent goal

        val state' = Lcf.|> (subgoals', validation')
      in
        (goal', state')
      end
      handle _ => raise Fail "Resusc"

      fun extract (Lcf.|> (_, validation)) =
        case outb validation of
           _ \ term => term
    end
end

structure MiniSig_ : MINI_SIGNATURE = MiniSig
