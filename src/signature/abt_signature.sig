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

  include SIGNATURE

  val def : sign -> def -> decl
  val undef : decl -> def
end
