signature DEVELOPMENT =
sig
  structure Abt : ABT

  type opid
  type symctx = Abt.symbol * Abt.sort

  datatype decl =
      DEFN of opid * symctx * Abt.metacontext * Abt.abt
    | THM of opid * symctx * Abt.abt

  type development = decl list

  val valid : development -> unit
end
