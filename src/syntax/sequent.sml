structure DimCtx = SplaySet (structure Elem = Symbol)

structure Sequent :> SEQUENT
  where type expr = RedPrlAbt.abt
  where type prop = RedPrlAbt.abt
  where type sort = RedPrlAtomicSort.t
  where type var = RedPrlAbt.variable
  where type sym = RedPrlAbt.symbol
  where type metactx = RedPrlAbt.metactx
  where type hypctx = (RedPrlAbt.abt * RedPrlAtomicSort.t) SymbolTelescope.telescope
  where type dimctx = DimCtx.set =
struct
  open RedPrlAbt
  type sort = RedPrlAtomicSort.t
  type prop = abt
  type expr = abt
  type var = variable
  type sym = symbol

  structure MetaCtx = Metavariable.Ctx and SymCtx = Symbol.Ctx and VarCtx = Variable.Ctx
  structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = RedPrlValence)

  type hypctx = (prop * sort) SymbolTelescope.telescope
  type dimctx = DimCtx.set

  datatype context =
    CONTEXT of
      {metactx : metactx Susp.susp,
       hypctx : hypctx,
       dimctx : dimctx}

  fun hypsMetactx H =
    SymbolTelescope.foldl
      (fn ((a, _), psi) => MetaCtxUtil.union (psi, metactx a))
      MetaCtx.empty
      H

  val emptyContext =
    CONTEXT
      {metactx = Susp.delay (fn _ => MetaCtx.empty),
       hypctx = SymbolTelescope.empty,
       dimctx = DimCtx.empty}

  fun getHyps (CONTEXT {hypctx,...}) =
    hypctx

  fun updateHyps f (CONTEXT {metactx, hypctx, dimctx}) =
    let
      val H = f hypctx
    in
      CONTEXT
        {metactx = Susp.delay (fn _ => hypsMetactx H),
         hypctx = H,
         dimctx = dimctx}
    end

  (* A sequent consists in a context (of metavariables, symbols and hypotheses)
   * and a conclusion [(P,tau)], where [tau] is the sort of the evidence to be
   * produced, and [P] is a type that refines [tau] which shall classify the
   * evidence. *)

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort
    | EQ_MEM of expr * expr * prop
    | MEM of expr * prop
    | EQ_SYN of expr * expr
    | SYN of expr

  datatype judgment =
      >> of context * concl (* categorical sequent *)
    | |> of ((sym * sort) list * (var * sort) list) * judgment (* parametric-generic sequent *)

  infix 4 >>
  infix 3 |>

  val conclMetactx =
    fn TRUE (p, _) => metactx p
     | TYPE (p, _) => metactx p
     | EQ_MEM (m, n, a) => MetaCtxUtil.union (MetaCtxUtil.union (metactx m, metactx n), metactx a)
     | MEM (m, a) => MetaCtxUtil.union (metactx m, metactx a)
     | EQ_SYN (r, s) => MetaCtxUtil.union (metactx r, metactx s)
     | SYN r => metactx r

  val rec judgmentMetactx =
    fn G |> jdg => judgmentMetactx jdg
     | CONTEXT {hypctx,...} >> concl => MetaCtxUtil.union (hypsMetactx hypctx, conclMetactx concl)

  structure Syn = RedPrlAbtSyntax
  val conclToString =
    fn TRUE (a, tau) => Syn.toString a ^ " true"
     | TYPE (a, tau) => Syn.toString a ^ " type"
     | EQ_MEM (m, n, a) => Syn.toString m ^ " = " ^ Syn.toString n ^ " : " ^ Syn.toString a
     | MEM (m, a) => Syn.toString m ^ " : " ^ Syn.toString a
     | EQ_SYN (r, s) => Syn.toString r ^ " = " ^ Syn.toString s ^ " synth"
     | SYN r => Syn.toString r ^ " synth"

  fun hypothesesToString H =
    let
      open SymbolTelescope open ConsView
      val rec go =
        fn EMPTY => ""
         | CONS (x, (a, tau), tl) =>
             let
               val hyp = Symbol.toString x ^ " : " ^ Syn.toString a
             in
               hyp ^ "\n" ^ go (out tl)
             end
    in
      go (out H)
    end

  fun toString ((Y, G) |> jdg) =
        "{" ^ ListSpine.pretty (fn (u, _) => Symbol.toString u) "," Y ^ "}"
          ^ "[" ^ ListSpine.pretty (fn (x, _) => Variable.toString x) "," G ^ "] |\n"
          ^ toString jdg
    | toString (H >> concl) =
        hypothesesToString (getHyps H)
          ^ "\226\138\162 "
          ^ conclToString concl
end
