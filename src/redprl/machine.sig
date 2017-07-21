signature REDPRL_MACHINE = 
sig
  type sign
  type abt

  exception Unstable

  (* All computation commutes with permutations of dimension names, but some computation
     involves observations that are not preserved by general substitutions of dimensions.
     
     Our machine can be run with respect to these two notions of 'stability'; NOMINAL
     stability is the most permissive, whereas steps observed under CUBICAL must always
     commute with cubical substitutions. If the machine is run under CUBICAL stability
     and an unstable observation is made, the Unstable exception is raised.*)
  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable

  exception Stuck
  exception Neutral of blocker

  datatype canonicity =
     CANONICAL
   | NEUTRAL of blocker
   | REDEX
   | STUCK
   | UNSTABLE

  val eval : sign -> stability -> abt -> abt

  (* Execute a term for 'n' steps; compatibility/congruence steps don't count. *)
  val steps : sign -> stability -> int -> abt -> abt

  val canonicity : sign -> stability -> abt -> canonicity
end