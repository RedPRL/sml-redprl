signature SYNTAX_VIEW =
sig
  type symbol
  type variable
  type metavariable
  type sort
  type 'a operator
  type 'a spine

  type term

  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a

  datatype 'a view =
     ` of variable
   | $ of symbol operator * 'a bview spine
   | $# of metavariable * ((symbol * sort) spine * 'a spine)

  val check : sort -> term view -> term
  val $$ : symbol operator * term bview spine -> term
  val out : term -> term view
end

functor AbtSyntaxView (Abt : ABT) : SYNTAX_VIEW =
struct
  open Abt
  type 'a operator = 'a Abt.O.t
  type term = abt
  fun check tau m = Abt.check (m, tau)
end

functor AstSyntaxView (Ast : AST where type 'a spine = 'a list) : SYNTAX_VIEW =
struct
  type symbol = Ast.symbol
  type variable = Ast.variable
  type metavariable = Ast.metavariable
  type sort = unit
  type 'a operator = 'a Ast.operator
  type 'a spine = 'a Ast.spine

  type term = Ast.ast

  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a

  datatype 'a view =
     ` of variable
   | $ of symbol operator * 'a bview spine
   | $# of metavariable * ((symbol * sort) spine * 'a spine)

  fun check () =
    fn `x => Ast.` x
     | $ (th, es) => Ast.$ (th, List.map (fn \ ((us,xs), m) => Ast.\ ((us, xs), m)) es)
     | $# (x, (us, ms)) => Ast.$# (x, (List.map #1 us, ms))

  fun $$ (th, es) = check () ($ (th, es))

  val out =
    fn Ast.`x => `x
     | Ast.$ (th, es) => $ (th, List.map (fn Ast.\ ((us, xs), m) => \ ((us, xs), m)) es)
     | Ast.$# (x, (us, ms)) => $# (x, (List.map (fn u => (u, ())) us, ms))
end

functor RedPRLSyntax (View : SYNTAX_VIEW where type 'a operator = 'a RedPRLOperator.t where type 'a spine = 'a list) =
struct

  open View

  structure O = RedPRLOperator
  structure RS = SortData

  datatype 'a view =
     CAPPROX of RS.sort * 'a * 'a
   | CEQUIV of RS.sort * 'a * 'a
   | BASE of RS.sort
   | TOP of RS.sort
   | UNIV of RS.sort
   | UNIV_GET_LVL of 'a
   | MEMBER of RS.sort * 'a * 'a
   | EQ of RS.sort * 'a * 'a * 'a
   | AX
   | SQUASH of RS.sort * 'a
   | DFUN of 'a * variable * 'a
   | FUN of 'a * 'a
   | NOT of 'a
   | LAM of variable * 'a
   | AP of 'a * 'a
   | DFUN_DOM of 'a
   | DFUN_COD of 'a * 'a
   | ENSEMBLE of RS.sort * RS.sort * 'a * variable * 'a
   | DEP_ISECT of 'a * variable * 'a
   | VOID

   | LBASE
   | LSUCC of 'a
   | LSUP of 'a * 'a


  infix 3 $ $$
  infix 2 \

  local
    fun @@ (f, x) = f x
    infix @@

    open RedPRLOperators

    fun ret tau m =
      O.RET tau $$ [([],[]) \ m]

    fun intoCttV th es =
      ret RS.EXP @@ O.V (CTT_V th) $$ es

    fun intoCttD th es =
      O.D (CTT_D th) $$ es

    fun cutCtt (sigma, tau) th es m =
      O.CUT (sigma, tau) $$ [([],[]) \ O.K (CTT_K th) $$ es, ([],[]) \ m]

    fun cutLvl th es m =
      O.CUT (RS.LVL, RS.LVL) $$ [([],[]) \ O.K (LVL_K th) $$ es, ([],[]) \ m]

  in
    val into =
      fn CAPPROX (tau, m, n) =>
          intoCttV (CttOperators.CAPPROX tau) [([],[]) \ m, ([],[]) \ n]
       | CEQUIV (tau, m, n) =>
          intoCttV (CttOperators.CEQUIV tau) [([],[]) \ m, ([],[]) \ n]
       | BASE tau =>
          intoCttV (CttOperators.BASE tau) []
       | TOP tau =>
          intoCttV (CttOperators.TOP tau) []
       | UNIV tau =>
          intoCttV (CttOperators.UNIV tau) []
       | UNIV_GET_LVL a =>
          cutCtt (RS.EXP, RS.LVL) CttOperators.UNIV_GET_LVL [] a
       | MEMBER (tau, m, a) =>
          intoCttV (CttOperators.MEMBER tau) [([],[]) \ m, ([],[]) \ a]
       | EQ (tau, m, n, a) =>
          intoCttV (CttOperators.EQ tau) [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | AX =>
          intoCttV CttOperators.AX []
       | SQUASH (tau, a) =>
          intoCttV (CttOperators.SQUASH tau) [([],[]) \ a]
       | DFUN (a, x, bx) =>
          intoCttV CttOperators.DFUN [([],[]) \ a, ([],[x]) \ bx]
       | FUN (a, b) =>
          intoCttD CttOperators.FUN [([],[]) \ a, ([],[]) \ b]
       | NOT a =>
          intoCttD CttOperators.NOT [([],[]) \ a]
       | ENSEMBLE (sigma, tau, a, x, bx) =>
          intoCttV (CttOperators.ENSEMBLE (sigma, tau)) [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) =>
          intoCttV CttOperators.LAM [([],[x]) \ mx]
       | AP (m, n) =>
          cutCtt (RS.EXP, RS.EXP) CttOperators.AP [([],[]) \ n] m
       | DFUN_DOM a =>
          cutCtt (RS.EXP, RS.EXP) CttOperators.DFUN_DOM [] a
       | DFUN_COD (a, b) =>
          cutCtt (RS.EXP, RS.EXP) CttOperators.DFUN_COD [([],[]) \ b] a
       | DEP_ISECT (a, x, bx) =>
          intoCttV CttOperators.DEP_ISECT [([],[]) \ a, ([],[x]) \ bx]
       | VOID =>
          intoCttV CttOperators.VOID []
       | LBASE =>
          ret RS.LVL @@ O.V (LVL_V 0) $$ []
       | LSUCC m =>
          cutLvl LevelOperators.LSUCC [] m
       | LSUP (m, n) =>
          cutLvl LevelOperators.LSUP0 [([],[]) \ n] m


    local
      fun outVal v =
        case View.out v of
           O.V (CTT_V (CttOperators.CAPPROX tau)) $ [_ \ m, _ \ n] => CAPPROX (tau, m, n)
         | O.V (CTT_V (CttOperators.CEQUIV tau)) $ [_ \ m, _ \ n] => CEQUIV (tau, m, n)
         | O.V (CTT_V (CttOperators.BASE tau)) $ _ => BASE tau
         | O.V (CTT_V (CttOperators.TOP tau)) $ _ => TOP tau
         | O.V (CTT_V (CttOperators.UNIV tau)) $ _ => UNIV tau
         | O.V (CTT_V (CttOperators.MEMBER tau)) $ [_ \ m, _ \ a] => MEMBER (tau, m, a)
         | O.V (CTT_V (CttOperators.EQ tau)) $ [_ \ m, _ \ n, _ \ a] => EQ (tau, m, n, a)
         | O.V (CTT_V CttOperators.AX) $ _ => AX
         | O.V (CTT_V (CttOperators.SQUASH tau)) $ [_ \ a] => SQUASH (tau, a)
         | O.V (CTT_V CttOperators.DFUN) $ [_ \ a, (_, [x]) \ bx] => DFUN (a, x, bx)
         | O.V (CTT_V (CttOperators.ENSEMBLE (sigma, tau))) $ [_ \ a, (_, [x]) \ bx] => ENSEMBLE (sigma, tau, a, x, bx)
         | O.V (CTT_V CttOperators.LAM) $ [(_, [x]) \ mx] => LAM (x, mx)
         | O.V (CTT_V CttOperators.DEP_ISECT) $ [_ \ a, (_, [x]) \ bx] => DEP_ISECT (a, x, bx)
         | O.V (CTT_V CttOperators.VOID) $ _ => VOID
         | _ => raise Fail "outVal expected value"

      fun outCut k m =
        case View.out k of
           O.K (CTT_K CttOperators.AP) $ [_ \ n] => AP (m, n)
         | O.K (CTT_K CttOperators.DFUN_DOM) $ _ => DFUN_DOM m
         | O.K (CTT_K CttOperators.DFUN_COD) $ [_ \ b] => DFUN_COD (m, b)
         | O.K (CTT_K CttOperators.UNIV_GET_LVL) $ _ => UNIV_GET_LVL m
         | O.K (LVL_K LevelOperators.LSUCC) $ _ => LSUCC m
         | O.K (LVL_K LevelOperators.LSUP0) $ [_ \ n] => LSUP (m, n)
         | O.K (LVL_K LevelOperators.LSUP1) $ [_ \ n] => LSUP (n, m)
         | _ => raise Fail "outCut expected continuation"

      fun outDef th es =
        case (th, es) of
           (CTT_D CttOperators.FUN, [_ \ a, _ \ b]) => FUN (a, b)
         | (CTT_D CttOperators.NOT, [_ \ a]) => NOT a
         | _ => raise Fail "outDef expected definitional extension"

    in
      fun out m =
        case View.out m of
           O.RET _ $ [_ \ v] => outVal v
         | O.CUT _ $ [_ \ k, _ \ m] => outCut k m
         | O.D th $ es => outDef th es
         | _ => raise Fail "Syntax view expected application expression"
    end
  end
end

structure RedPRLAbtSyntax = RedPRLSyntax (AbtSyntaxView (RedPRLAbt))
structure RedPRLAstSyntax = RedPRLSyntax (AstSyntaxView (RedPRLAst))
