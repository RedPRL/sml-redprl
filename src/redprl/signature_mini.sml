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
  type proof_state = Lcf.jdg Lcf.state
  type jdg = RedPrlJudgment.jdg

  type 'a params = ('a * psort) list
  type 'a arguments = ('a * valence) list

  type src_opid = string
  type entry =
    {sourceOpid : src_opid,
     params : symbol params,
     arguments : metavar arguments,
     sort : sort,
     spec : jdg option,
     state : Lcf.jdg Lcf.state}

  datatype src_decl =
      DEF of {arguments : string arguments, params : string params, sort : sort, definiens : ast}
    | THM of {arguments : string arguments, params : string params, goal : ast, script : ast}
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
    case E.run (ETelescope.lookup elabSign opid) of
        SOME (EDEF defn) => defn
      | _ => raise Fail "Elaboration failed"

  fun unifyCustomOperator (entry : entry) (ps : Tm.param list) (es : abt Tm.bview list) : Tm.metaenv * Tm.symenv =
    let
      val {params, arguments, ...} = entry
      val srho = ListPair.foldl (fn ((u, _), p, ctx) => Sym.Ctx.insert ctx u p) Sym.Ctx.empty (params, ps)
      val mrho = ListPair.foldl (fn ((x, vl), e, ctx) => Metavar.Ctx.insert ctx x (Tm.checkb (e, vl))) Metavar.Ctx.empty (arguments, es)
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
            RedPrlParamData.HYP =>
              let
                val RedPrlParameterTerm.VAR v = ptm
              in
                Var.Ctx.insert ctx u (Tm.check (Tm.`v, RedPrlOpData.EXP))
              end
          | _ => ctx
      in
        ListPair.foldl handleHyp Var.Ctx.empty (#params entry, ps)
      end

    fun relabelHyp (u, v) H =
      let
        val jdg = Hyps.lookup H u
        val H' = Hyps.interposeAfter H u (Hyps.singleton v jdg)
      in
        Hyps.remove u H'
      end

    fun relabelHyps (entry : entry) (ps : Tm.param list) H = 
      let
        fun handleHyp ((u, psort), ptm, H) =
          case psort of 
             RedPrlParamData.HYP =>
               let
                 val RedPrlParameterTerm.VAR v = ptm
               in
                 relabelHyp (u, v) H
               end
           | _ => H
      in
        ListPair.foldl handleHyp H (#params entry, ps)
      end

    fun relabelSequent (entry : entry) (ps : Tm.param list) : abt jdg -> abt jdg =
      fn H >> catjdg => relabelHyps entry ps H >> catjdg
      | jdg => jdg
  in
    fun resuscitateTheorem sign opid ps args = 
      let
        val entry = lookup sign opid
        val paramsSig = #params entry
        val argsSig = #arguments entry
        val SOME goal = #spec entry
        val state as Lcf.|> (subgoals, validation) = #state entry

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

      fun extract (Lcf.|> (subgoals, validation)) = 
        case outb validation of 
           ([],[]) \ term => term
         | _ => raise Fail "Extract term has unexpected binder. Can this relaly happen?"
    end
end

structure MiniSig_ : MINI_SIGNATURE = MiniSig