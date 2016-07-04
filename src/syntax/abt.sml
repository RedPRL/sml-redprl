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

structure RedPrlOperator : JSON_LCS_OPERATOR =
struct
  local
    structure O = LcsOperator (RedPrlLcs)
    structure J = Json and AS = RedPrlAtomicSortJson and V = RedPrlV and K = RedPrlK and D = RedPrlD
  in
    open O

    fun ** (SOME a, SOME b) = SOME (a, b)
      | ** _ = NONE

    infix **

  fun traverseOpt f xs =
    SOME (List.map (Option.valOf o f) xs)
      handle _ => NONE

    fun encodeSymAnn f (a, tau) =
      J.Array [f a, AS.encode tau]

    fun decodeSymAnn f =
      fn J.Array [a, tau] => f a ** AS.decode tau
       | _ => NONE

    fun encodeValence ((sigmas, taus), tau) =
      J.Obj
        [("syms", J.Array (List.map AS.encode sigmas)),
         ("vars", J.Array (List.map AS.encode taus)),
         ("sort", AS.encode tau)]

    val decodeValence =
      fn J.Obj [("syms", J.Array syms), ("vars", J.Array vars), ("sort", sort)] => traverseOpt AS.decode syms ** traverseOpt AS.decode vars ** AS.decode sort
       | _ => NONE

    fun encodeArity (valences, tau) =
      J.Obj
        [("valences", J.Array (List.map encodeValence valences)),
         ("sort", AS.encode tau)]

    val decodeArity =
      fn J.Obj [("valences", J.Array valences), ("sort", sort)] => traverseOpt decodeValence valences ** AS.decode sort
       | _ => NONE

    fun encode f =
      fn V th => J.Obj [("v", V.encode f th)]
       | K th => J.Obj [("k", K.encode f th)]
       | D th => J.Obj [("d", D.encode f th)]
       | RET tau => J.Obj [("ret", AS.encode tau)]
       | CUT (sigma, tau) => J.Obj [("cut", J.Array [AS.encode sigma, AS.encode tau])]
       | ESUBST (symAnns, varSorts, tau) => J.Obj [("esubst", J.Obj [("syms", J.Array (List.map (encodeSymAnn f) symAnns)), ("vars", J.Array (List.map AS.encode varSorts)), ("sort", AS.encode tau)])]
       | CUSTOM (opid, params, arity) => J.Obj [("custom", J.Obj [("opid", f opid), ("params", J.Array (List.map (encodeSymAnn f) params)), ("arity", encodeArity arity)])]

    fun decode f =
      fn J.Obj [("v", th)] => Option.map V (V.decode f th)
       | J.Obj [("k", th)] => Option.map K (K.decode f th)
       | J.Obj [("d", th)] => Option.map D (D.decode f th)
       | J.Obj [("ret", tau)] => Option.map RET (AS.decode tau)
       | J.Obj [("cut", J.Array [sigma, tau])] => Option.map CUT (AS.decode sigma ** AS.decode tau)
       | J.Obj [("esubst", J.Obj [("syms", J.Array syms), ("vars", J.Array vars), ("sort", sort)])] =>
           Option.map
             (fn ((x, y), z) => ESUBST (x, y, z))
             (traverseOpt (decodeSymAnn f) syms ** traverseOpt AS.decode vars ** AS.decode sort)
       | J.Obj [("custom", J.Obj [("opid", opid), ("params", J.Array params), ("arity", arity)])] =>
           Option.map
             (fn ((x,y), z) => CUSTOM (x, y, z))
             (f opid ** traverseOpt (decodeSymAnn f) params ** decodeArity arity)
       | _ => NONE
  end
end

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
