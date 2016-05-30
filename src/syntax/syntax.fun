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
  val infer : term -> term view * sort
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

  fun infer m =
    (out m, ())
end

functor RedPRLSyntax (View : SYNTAX_VIEW where type 'a operator = 'a RedPRLOperator.t where type 'a spine = 'a list) =
struct

  open View

  structure O = RedPRLOperator
  structure RS = SortData

  datatype 'a view =
     CAPPROX of O.S.atomic * 'a * 'a
   | CEQUIV of O.S.atomic * 'a * 'a
   | BASE of O.S.atomic
   | TOP of O.S.atomic
   | UNIV of O.S.atomic
   | UNIV_GET_LVL of 'a
   | MEMBER of O.S.atomic * 'a * 'a
   | EQ of O.S.atomic * 'a * 'a * 'a
   | AX
   | SQUASH of O.S.atomic * 'a
   | DFUN of 'a * variable * 'a
   | FUN of 'a * 'a
   | NOT of 'a
   | LAM of variable * 'a
   | AP of 'a * 'a
   | DFUN_DOM of 'a
   | ENSEMBLE of O.S.atomic * O.S.atomic * 'a * variable * 'a
   | DEP_ISECT of 'a * variable * 'a
   | VOID


  infix 3 $$
  infix 2 \

  local
    fun @@ (f, x) = f x
    infix @@

    fun ret tau m =
      O.RET tau $$ [([],[]) \ m]

    fun intoCttV th es =
      ret RS.EXP @@ O.V (RedPRLOperators.CTT_V th) $$ es

    fun intoCttD th es =
      O.D (RedPRLOperators.CTT_D th) $$ es

    fun cutCtt (sigma, tau) th es m =
      O.CUT (sigma, tau) $$ [([],[]) \ O.K (RedPRLOperators.CTT_K th) $$ es, ([],[]) \ m]
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
       | DEP_ISECT (a, x, bx) =>
          intoCttV CttOperators.DEP_ISECT [([],[]) \ a, ([],[x]) \ bx]
       | VOID =>
          intoCttV CttOperators.VOID []

  end
end

structure RedPRLAbtSyntax = RedPRLSyntax (AbtSyntaxView (RedPRLAbt))
structure RedPRLAstSyntax = RedPRLSyntax (AstSyntaxView (RedPRLAst))
