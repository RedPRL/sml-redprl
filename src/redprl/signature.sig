signature SIGNATURE = 
sig
  type sort
  type ast

  (* source language: to be phased out *)
  structure Src :
  sig
    type arguments = (string * Tm.valence) list
    type elt = MlExtSyntax.cmd -> MlExtSyntax.cmd
    type sign = elt list
  end

  val checkSrcSig : Src.sign -> bool
end
