structure Metavariable = AbtSymbol ()

structure Symbol = AbtSymbol ()

(* it will come in handy for variables and symbols to be of the same type *)
structure Variable = Symbol

structure OptionUtil =
struct
  fun traverseOpt f xs =
    SOME (List.map (Option.valOf o f) xs)
      handle _ => NONE

  fun ** (SOME a, SOME b) = SOME (a, b)
    | ** _ = NONE
end

structure Semivalence =
struct
  structure J = Json and AS = RedPrlAtomicSortJson
  open OptionUtil
  infix **

  fun encode (sigmas, sigma) =
    J.Obj [("syms", J.Array (List.map AS.encode sigmas)), ("sort", AS.encode sigma)]

  val decode =
    fn J.Obj [("syms", J.Array sigmas), ("sort", sigma)] => traverseOpt AS.decode sigmas ** AS.decode sigma
     | _ => NONE
end

structure RedPrlSort =
struct
  local
    structure S = LcsSort (structure AtomicSort = RedPrlAtomicSort val opidSort = SOME SortData.OPID)
    structure J = Json and AS = RedPrlAtomicSortJson

    fun ** (SOME a, SOME b) = SOME (a, b)
      | ** _ = NONE

    infix **
  in
    open S

    val encodeSort =
      fn EXP tau => J.Obj [("exp", AS.encode tau)]
       | VAL tau => J.Obj [("val", AS.encode tau)]
       | CONT (svl, tau) => J.Obj [("cont", J.Array [Semivalence.encode svl, AS.encode tau])]

    val decodeSort =
      fn J.Obj [("exp", tau)] => Option.map EXP (AS.decode tau)
       | J.Obj [("val", tau)] => Option.map VAL (AS.decode tau)
       | J.Obj [("cont", J.Array [svl, tau])] => Option.map CONT (Semivalence.decode svl ** AS.decode tau)
       | _ => NONE
  end
end

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
    open O OptionUtil
    infix **

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
       | CUT (svl, tau) => J.Obj [("cut", J.Array [Semivalence.encode svl, AS.encode tau])]
       | ESUBST (symAnns, varSorts, tau) => J.Obj [("esubst", J.Obj [("syms", J.Array (List.map (encodeSymAnn f) symAnns)), ("vars", J.Array (List.map AS.encode varSorts)), ("sort", AS.encode tau)])]
       | CUSTOM (opid, params, arity) => J.Obj [("custom", J.Obj [("opid", f opid), ("params", J.Array (List.map (encodeSymAnn f) params)), ("arity", encodeArity arity)])]

    fun decode f =
      fn J.Obj [("v", th)] => Option.map V (V.decode f th)
       | J.Obj [("k", th)] => Option.map K (K.decode f th)
       | J.Obj [("d", th)] => Option.map D (D.decode f th)
       | J.Obj [("ret", tau)] => Option.map RET (AS.decode tau)
       | J.Obj [("cut", J.Array [svl, tau])] => Option.map CUT (Semivalence.decode svl ** AS.decode tau)
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

structure RedPrlAbtJsonKit : ABT_JSON_KIT =
struct
  structure Abt = RedPrlAbt

  local
    structure J = Json and AS = RedPrlAtomicSortJson
    open RedPrlOperator.S

    fun ** (SOME a, SOME b) = SOME (a, b)
      | ** _ = NONE

    infix **
  in
    val encodeSort =
      fn EXP tau => J.Obj [("exp", AS.encode tau)]
       | VAL tau => J.Obj [("val", AS.encode tau)]
       | CONT (svl, tau) => J.Obj [("cont", J.Array [Semivalence.encode svl, AS.encode tau])]

    val decodeSort =
      fn J.Obj [("exp", tau)] => Option.map EXP (AS.decode tau)
       | J.Obj [("val", tau)] => Option.map VAL (AS.decode tau)
       | J.Obj [("cont", J.Array [svl, tau])] => Option.map CONT (Semivalence.decode svl ** AS.decode tau)
       | _ => NONE
  end

  val encodeOperator = RedPrlOperator.encode
  val decodeOperator = RedPrlOperator.decode
end

structure RedPrlAbtJson = AbtJson (RedPrlAbtJsonKit)

structure RedPrlAstToAbt =
  AstToAbt
    (structure Ast = RedPrlAst
     structure Abt = RedPrlAbt)

structure ShowAbt = PlainShowAbt (RedPrlAbt)
structure DebugShowAbt = DebugShowAbt (RedPrlAbt)
