signature ABT_SIGNATURE =
sig
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

  val def : def -> decl
end
