signature ABT_SIGNATURE =
sig
  structure Abt : ABT
  type term = Abt.abt
  type symbol = Abt.symbol
  type sort = Abt.sort
  type metavariable = Abt.metavariable
  type valence = Abt.valence
  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  structure Decl :
  sig
    datatype decl = DEF of def | SYMDCL of sort
  end

  include SIGNATURE

  val def : sign -> def -> decl
  val symdcl : sign -> sort -> decl

  val viewDecl : decl -> Decl.decl
end
