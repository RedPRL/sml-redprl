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

  type 'a params = ('a * psort) list
  type 'a arguments = ('a * valence) list

  type src_opid = string
  type entry =
    {sourceOpid : src_opid,
     params : symbol params,
     arguments : metavar arguments,
     sort : sort,
     definiens : Lcf.jdg Lcf.state}

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
end