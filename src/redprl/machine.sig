signature REDPRL_MACHINE = 
sig
  type sign
  type abt
  type opid

  exception Unstable

  (* All computation commutes with permutations of dimension names, but some computation
     involves observations that are not preserved by general substitutions of dimensions.
     
     Our machine can be run with respect to these two notions of 'stability'; NOMINAL
     stability is the most permissive, whereas steps observed under STABLE must always
     commute with cubical substitutions. If the machine is run under STABLE stability
     and an unstable observation is made, the Unstable exception is raised.*)
  datatype stability = 
     STABLE
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable
   | OPERATOR of opid

  exception Stuck
  exception Neutral of blocker

  datatype canonicity =
     CANONICAL
   | NEUTRAL of blocker
   | REDEX
   | STUCK
   | UNSTABLE

  structure Unfolding :
  sig
    type regime = opid -> bool

    (* Don't unfold operators for which we have type information! *)
    val default : sign -> regime

    (* Don't unfold any operators *)
    val never : regime

    (* Always unfold operators *)
    val always : regime
  end

  val eval : sign -> stability -> Unfolding.regime -> abt -> abt

  (* Execute a term for 'n' steps; compatibility/congruence steps don't count. *)
  val steps : sign -> stability -> Unfolding.regime -> int -> abt -> abt

  val canonicity : sign -> stability -> Unfolding.regime -> abt -> canonicity
end
