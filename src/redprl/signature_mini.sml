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

  type names = int -> symbol
  type src_opid = string
  type entry =
    {sourceOpid : src_opid,
     spec : jdg,
     state : names -> Lcf.jdg Lcf.state}

  type src_catjdg = RedPrlCategoricalJudgment.astjdg
  type src_seqhyp = string * src_catjdg
  type src_sequent = src_seqhyp list * src_catjdg
  type src_genjdg = (string * psort) list * src_sequent
  type src_rulespec = src_genjdg list * src_sequent

  datatype src_decl =
      DEF of {arguments : string arguments, params : string params, sort : sort, definiens : ast}
    | THM of {arguments : string arguments, params : string params, goal : src_sequent, script : ast}
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

  fun entryParams (entry : entry) : symbol params = 
    let
      val RedPrlSequent.>> ((I, _), _) = #spec entry
    in
      I
    end

  fun entryArguments (entry : entry) : metavar arguments =
    let
      val Lcf.|> (subgoals, _) = #state entry (fn _ => Sym.new ())
    in
      Lcf.Tl.foldr (fn (x, jdg, args) => (x, RedPrlJudgment.sort jdg) :: args) [] subgoals
    end

  fun entrySort (entry : entry) : sort = 
    let
      val RedPrlSequent.>> (_, jdg) = #spec entry
    in
      RedPrlCategoricalJudgment.synthesis jdg
    end

  fun applyCustomOperator (entry : entry) (ps : Tm.param list) (es : abt Tm.bview list) : Tm.metaenv * Tm.symenv =
    let
      val params = entryParams entry
      val arguments = entryArguments entry
      val srho = ListPair.foldl (fn ((u, _), p, ctx) => Sym.Ctx.insert ctx u p) Sym.Ctx.empty (params, ps)
      val mrho = ListPair.foldl (fn ((x, vl), e, ctx) => Metavar.Ctx.insert ctx x (Tm.checkb (e, vl))) Metavar.Ctx.empty (arguments, es)
    in
      (mrho, srho)
    end

  fun extract (Lcf.|> (_, validation)) =
    case RedPrlAbt.outb validation of
       RedPrlAbt.\ (_, term) => term
end

structure MiniSig_ : MINI_SIGNATURE = MiniSig
