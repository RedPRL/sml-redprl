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
  type opid = RedPrlOpData.opid
  type jdg = RedPrlJudgment.jdg

  type 'a arguments = ('a * valence) list

  type names = int -> symbol
  type src_opid = string
  type entry =
    {sourceOpid : src_opid,
     spec : jdg,
     state : names -> Lcf.jdg Lcf.state}

  type src_catjdg = ast
  type src_seqhyp = string * src_catjdg
  type src_sequent = src_seqhyp list * src_catjdg
  type src_genjdg = (string * psort) list * src_sequent

  datatype src_decl =
      DEF of {arguments : string arguments, sort : sort, definiens : ast}
    | THM of {arguments : string arguments, goal : src_sequent, script : ast}
    | TAC of {arguments : string arguments, script : ast}

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
  structure NameEnv = AstToAbt.NameEnv

  (* A signature / [sign] is a telescope of declarations. *)
  type src_sign = (src_decl * Pos.t option) Telescope.telescope

  (* An elaborated signature is a telescope of definitions. *)
  type elab_sign = elab_decl ElabMonad.t Telescope.telescope

  type sign =
    {sourceSign : src_sign,
     elabSign : elab_sign,
     nameEnv : Tm.symbol NameEnv.dict}

  structure E = ElabMonadUtil (ElabMonad)
  fun lookup ({elabSign, ...} : sign) opid =
    case E.run (Telescope.lookup elabSign opid) of
        SOME (EDEF defn) => defn
      | _ => raise Fail "Elaboration failed"

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
      RedPrlAtomicJudgment.synthesis jdg
    end

  fun unfoldCustomOperator (entry : entry) (es : abt Tm.bview list) : abt =
    let
      val arguments = entryArguments entry
      val Lcf.|> (_, evd) = #state entry (fn _ => Sym.new ())
      val Tm.\ ((us, []), term) = Tm.outb evd
      val mrho = ListPair.foldlEq  (fn ((x, vl), e, ctx) => Metavar.Ctx.insert ctx x (Tm.checkb (e, vl))) Metavar.Ctx.empty (arguments, es)
    in
      Tm.substMetaenv mrho term
    end
end

structure MiniSig_ : MINI_SIGNATURE = MiniSig
