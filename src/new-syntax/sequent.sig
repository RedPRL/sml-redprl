signature SEQUENT =
sig
  type var = RedPrlAbt.variable
  type sym = RedPrlAbt.symbol
  type hyp = sym

  structure Hyps : TELESCOPE where type Label.t = hyp

  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a ctx * 'a
   | |> of (var list * sym list) * 'a jdg

  val map : ('a -> 'b) jdg -> 'a jdg -> 'b jdg

  structure CJ : CATEGORICAL_JUDGMENT

  val judgmentMetactx : RedPrlAbt.abt CJ.jdg jdg -> RedPrlAbt.metactx
end
