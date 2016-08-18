signature ABT_SIGNATURE =
sig
  structure Abt : ABT
  type term = Abt.abt
  type symbol = Abt.symbol
  type sort
  type valence
  type metavariable = Abt.metavariable
  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term,
     pos : Pos.t option}

  structure Decl :
  sig
    datatype decl = DEF of def | SYM_DECL of sort
  end

  include SIGNATURE

  val def : sign -> def -> decl
  val symDecl : sign -> sort -> decl

  val viewDecl : decl -> Decl.decl

  val encode : sign -> Json.json_value
end
