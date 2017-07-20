functor NewMachine (Sig : MINI_SIGNATURE) :
sig
  type sign = Sig.sign
  type abt = RedPrlAbt.abt
  type 'a machine

  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable

  exception Neutral of blocker
  exception Unstable
  exception Final

  val init : abt -> abt machine
  val step : sign -> stability -> abt machine -> abt machine
end = 
struct
  structure Tm = RedPrlAbt
  structure Syn = Syntax
  structure SymSet = SplaySet (structure Elem = Sym.Ord)
  
  type sign = Sig.sign

  fun @@ (f, x) = f x
  infixr @@

  infix 6 <:
  infix 3 ||


  open Tm infix 7 $ $$ $# infix 6 \
  structure O = RedPrlOpData
  structure P = struct open RedPrlParameterTerm RedPrlSortData end

  datatype hole = HOLE
  datatype frame =
     APP of hole * abt
   | HCOM of symbol O.dir * hole * abt * (symbol O.equation * (symbol * abt)) list
   | COE of symbol O.dir * (symbol * hole) * abt
   | FST of hole
   | SND of hole
   | W_IF of (variable * abt) * hole * abt * abt
   | IF of hole * abt * abt

  type stack = frame list
  type bound_syms = SymSet.set

  datatype 'a machine = || of 'a * (bound_syms * stack)


  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of variable
   | METAVAR of metavariable

  exception Neutral of blocker
  exception Unstable
  exception Final

  val todo = Fail "TODO"
  fun ?e = raise e

  (* Is it safe to observe the identity of a dimension? *)
  fun dimensionSafeToObserve syms r = 
    case r of 
       P.VAR x => SymSet.member syms x
     | _ => true

  fun dimensionsEqual stability syms (r1, r2) = 
    (* If two dimensions are equal, then no substitution can ever change that. *)
    if P.eq Sym.eq (r1, r2) then 
      true
    else
      (* On the other hand, if they are not equal, this observation may not commute with cubical substitutions. *)
      case stability of 
          (* An observation of apartness is stable under permutations. *)
          NOMINAL => false
          (* An observation of apartness is only stable if one of the compared dimensions is bound. *)
        | CUBICAL =>
            if dimensionSafeToObserve syms r1 orelse dimensionSafeToObserve syms r2 then 
              false 
            else
              raise Unstable

  fun findTrueEquationIndex stability syms = 
    let
      fun aux i [] = NONE
        | aux i ((r,r') :: eqs) =
          if dimensionsEqual stability syms (r, r') then 
            SOME i
          else 
            aux (i + 1) eqs
    in
      aux 0
    end

  fun stepView sign stability tau =
    fn `x || stk => raise Neutral (VAR x)
     | x $# (rs, ms)|| stk => raise Neutral (METAVAR x)
     | _ => ?todo

  fun step sign stability (tm || stk) =
    let
      val (view, tau) = infer tm
    in
      stepView sign stability tau (view || stk)
    end

  fun init tm = 
    tm || (SymSet.empty, [])
end