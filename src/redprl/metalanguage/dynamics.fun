functor MetalanguageDynamics (ML : METALANGUAGE) :
sig
end = 
struct
  datatype hole = HOLE
  datatype ('a, 'b) closure = <: of 'a * ('b, 'b) closure ML.Ctx.dict
  
  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlCategoricalJudgment

  type mlterm = ML.mlterm_
  type mlscope = (ML.mlvar, mlterm) ML.mlscope

  datatype continuation =
     FUN of hole * mlterm
   | ARG of mlscope * hole
   | LET of ML.mlvar * hole * mlterm
   | PAIR0 of hole * mlterm
   | PAIR1 of mlterm * hole
   | FST of hole
   | SND of hole
   | EACH of {tactics: mlterm list, done: Lcf.jdg Lcf.Tl.telescope, metaenv: Tm.metaenv}
   | SPLICE of {tactics: mlterm list, var: Lcf.L.var, done: Lcf.jdg Lcf.Tl.telescope, remaining: Lcf.jdg Lcf.Tl.telescope, metaenv: Tm.metaenv}

  type stack = (continuation, mlterm) closure list

  type names = int -> Tm.symbol
  datatype state = LOCAL of Lcf.jdg | GLOBAL of Lcf.jdg Lcf.state
  datatype control = ## of (state * names) * (mlterm, mlterm) closure
  datatype machine = |> of control * stack | <| of control * stack

  infix 3 ##
  infix 6 <:
  infix 2 <| |>

  exception todo fun ?e = raise e

  structure Tactical = RedPrlTactical (Lcf)

  fun applyRule (rule : Rules.rule) (jdg, alpha) : state * names =
    let
      val (alpha', probe) = UniversalSpread.probe alpha
      val state' = rule alpha' jdg
      val beta = UniversalSpread.bite (!probe) alpha
    in
      (GLOBAL state', beta)
    end

  exception Final
  exception Stuck

  val step = 
    fn _ ## _ <: _ |> [] => raise Final
     | st ## ML.VAR x <: env <| ks => st ## ML.Ctx.lookup env x |> ks
     | st ## ML.LET (t, sc) <: env <| ks => 
       let
         val (x, tx) = ML.unscope sc
       in
         st ## t <: env <| LET (x, HOLE, tx) <: env :: ks
       end
     | st ## v <: env |> LET (x, HOLE, tx) <: env' :: ks => st ## tx <: ML.Ctx.insert env' x (v <: env) <| ks
     | st ## ML.LAM sc <: env <| ks => st ## ML.LAM sc <: env |> ks
     | st ## ML.APP (t1, t2) <: env <| ks => st ## t1 <: env <| FUN (HOLE, t2) <: env :: ks
     | st ## ML.LAM sc <: env |> FUN (HOLE, t) <: env' :: ks => st ## t <: env' <| ARG (sc, HOLE) <: env :: ks
     | st ## v <: env |> ARG (sc, HOLE) <: env' :: ks =>
       let
         val (x, tx) = ML.unscope sc
       in
         st ## tx <: ML.Ctx.insert env' x (v <: env) <| ks
       end
     | st ## ML.PAIR (t1, t2) <: env <| ks => st ## t1 <: env <| PAIR0 (HOLE, t2) <: env :: ks
     | st ## v <: env |> PAIR0 (HOLE, t) <: env' :: ks => st ## t <: env' <| PAIR1 (v, HOLE) <: env :: ks
     | st ## v <: env |> PAIR1 (v', HOLE) <: env' :: ks => 
       let
         val x = ML.freshVar ()
         val y = ML.freshVar ()
         val envxy = ML.Ctx.insert (ML.Ctx.singleton x (v' <: env')) y (v <: env)
       in
         st ## ML.PAIR (ML.VAR x, ML.VAR y) <: envxy |> ks
       end
     | st ## ML.FST t <: env <| ks => st ## t <: env |> FST HOLE <: env :: ks
     | st ## ML.SND t <: env <| ks => st ## t <: env |> SND HOLE <: env :: ks
     | st ## ML.PAIR (v1, _) <: env |> FST HOLE <: _ :: ks => st ## v1 <: env |> ks
     | st ## ML.PAIR (_, v2) <: env |> SND HOLE <: _ :: ks => st ## v2 <: env |> ks
     | st ## ML.QUOTE tm <: env <| ks => st ## ML.QUOTE tm <: env |> ks
     | (st as (LOCAL (J.>> (_, goal)), _)) ## ML.GOAL <: _ <| ks =>
       st ## ML.QUOTE (CJ.toAbt goal) <: ML.Ctx.empty |> ks
     | (LOCAL jdg, alpha) ## ML.REFINE ruleName <: env <| ks =>
       let
         val rule = Rules.lookupRule ruleName
         val st' = applyRule rule (jdg, alpha)
       in
         st' ## ML.NIL <: ML.Ctx.empty |> ks
       end
     | (st as (GLOBAL state, _)) ## ML.ALL t <: env <| ks =>
       let
         val Lcf.|> (psi, _) = state
         val ts = Lcf.Tl.foldr (fn (_, _, ts) => t::ts) [] psi
         val eachState = {tactics = ts, done = Lcf.Tl.empty, metaenv = Tm.Metavar.Ctx.empty}
       in
         st ## ML.NIL <: ML.Ctx.empty |> EACH eachState <: env :: ks
       end

     | (GLOBAL state, alpha) ## _ <: _ |> EACH {tactics, done, metaenv} <: env :: ks =>
       let
         val Lcf.|> (psi, evd) = state
         open Lcf.Tl.ConsView
       in
         case (out psi, tactics) of
            (EMPTY, []) => (GLOBAL (Lcf.|> (done, evd)), alpha) ## ML.NIL <: ML.Ctx.empty |> ks
          | (CONS (x, jdg, psi), t :: ts) =>
            let
              val jdg' = Lcf.J.subst metaenv jdg
              val spliceState = {tactics = ts, var = x, done = done, remaining = psi, metaenv = metaenv}
            in
              (LOCAL jdg', alpha) ## t <: env <| SPLICE spliceState <: env :: ks
            end
       end
     
     | (GLOBAL state, alpha) ## _ <: _ |> SPLICE {tactics, var = x, done, remaining, metaenv} <: env :: ks => 
       let
         val Lcf.|> (psi, evd) = state
         val metaenv' = Tm.Metavar.Ctx.insert metaenv x evd
         val state' = Lcf.|> (remaining, evd)
         val eachState = {tactics = tactics, done = Lcf.Tl.append psi done, metaenv = metaenv'}
       in
         (GLOBAL state', alpha) ## ML.NIL <: ML.Ctx.empty |> EACH eachState <: env :: ks
       end

     | _ => raise Stuck

  exception todo fun ?e = raise e
end