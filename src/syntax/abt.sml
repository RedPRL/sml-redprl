structure Metavariable = AbtSymbol ()

structure Symbol = AbtSymbol ()

(* it will come in handy for variables and symbols to be of the same type *)
structure Variable = Symbol

structure RedPrlSort =
  LcsSort
    (structure AtomicSort = RedPrlAtomicSort
     val opidSort = SOME SortData.OPID)

structure RedPrlLcs =
struct
  structure V = RedPrlV and K = RedPrlK and D = RedPrlD
  val opidSort = SOME SortData.OPID
  val input = RedPrlK.input
end

structure RedPrlOperator = LcsOperator (RedPrlLcs)
structure RedPrlArity = RedPrlOperator.Ar
structure RedPrlValence = RedPrlArity.Vl

structure RedPrlAst =
  Ast
    (structure Operator = RedPrlOperator
     structure Metavar = Metavariable)


structure RedPrlAbt =
  Abt
    (structure O = RedPrlOperator
     structure Metavar = Metavariable
     structure Var = Variable
     structure Sym = Symbol)

structure RedPrlAstToAbt =
  AstToAbt
    (structure Ast = RedPrlAst
     structure Abt = RedPrlAbt)

structure ShowAbt = PlainShowAbt (RedPrlAbt)
structure DebugShowAbt = DebugShowAbt (RedPrlAbt)
