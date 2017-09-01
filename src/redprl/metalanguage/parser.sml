structure Streamable =
  CoercedStreamable
    (structure Streamable = StreamStreamable
     type 'a item = 'a * Pos.t
     fun coerce (x, _) = x)


structure MetalanguageTerminal = 
struct
  type pos = Pos.t
  type pos_string = pos * string

  datatype terminal =
      LET of pos
    | FN of pos
    | VAL of pos
    | IN of pos
    | BY of pos
    | DOUBLE_RIGHT_ARROW of pos
    | LSQUARE of pos
    | RSQUARE of pos
    | LPAREN of pos
    | RPAREN of pos
    | COMMA of pos
    | SEMI of pos
    | COLON of pos
    | EQUALS of pos
    | BEGIN of pos
    | END of pos
    | IDENT of pos_string
    | PROVE of pos
    | PROJ1 of pos
    | PROJ2 of pos
    | BACKTICK of pos
    | REFINE of pos
    | GOAL of pos
    | PUSH of pos
    | PRINT of pos
    | EXACT of pos
    | EXP of pos
    | DIM of pos

  val terminalToString = 
    fn LET _ => "LET"
     | VAL _ => "VAL"
     | FN _ => "FN"
     | IN _ => "IN"
     | BY _ => "BY"
     | DOUBLE_RIGHT_ARROW _ => "DOUBLE_RIGHT_ARROW"
     | LSQUARE _ => "LSQUARE"
     | RSQUARE _ => "RSQUARE"
     | LPAREN _ => "LPAREN"
     | RPAREN _ => "RPAREN"
     | COMMA _ => "COMMA"
     | SEMI _ => "SEMI"
     | COLON _ => "COLON"
     | EQUALS _ => "EQUALS"
     | BEGIN _ => "BEGIN"
     | END _ => "END"
     | IDENT _ => "IDENT"
     | PROVE _ => "PROVE"
     | PROJ1 _ => "PROJ1"
     | PROJ2 _ => "PROJ2"
     | BACKTICK _ => "BACKTICK"
     | REFINE _ => "REFINE"
     | GOAL _ => "GOAL"
     | PUSH _ => "PUSH"
     | PRINT _ => "PRINT"
     | EXACT _ => "EXACT"
     | EXP _ => "exp"
     | DIM _ => "dim"

end

structure MetalanguageParseAction = 
struct
  structure ML = MetalanguageSyntax and Tm = RedPrlAbt
  open ML infix :@
  open MetalanguageTerminal

  type string = string
  type oexp = string RedExpr.expr
  type oexps = oexp list
  type exp = ML.src_mlterm
  type exps = ML.src_mlterm list
  type ident = pos * string
  type names = ident list
  type sorted_names = (ident * osort) list
  type decl = ident * ML.src_mlterm
  type decls = decl list

  fun @@ (f, x) = f x
  infixr @@ 

  exception hole
  fun ?e = raise e


  val mergeAnnotation = 
    fn (SOME x, SOME y) => SOME (Pos.union x y)
     | (NONE, SOME x) => SOME x
     | (SOME x, _) => SOME x
     | _ => NONE

  val posOfTerms : exp list -> ML.annotation =
    List.foldl
      (fn (_ :@ ann', ann) => mergeAnnotation (ann', ann))
      NONE

  fun namesNil () = []
  fun namesSingl x = [x]
  fun namesCons (x, xs) = x :: xs

  fun sortedNamesNil () = []
  fun sortedNamesSingl (x, tau) = [(x, tau)]
  fun sortedNamesCons (x, tau, xs) = (x, tau) :: xs

  fun expsNil () = []
  fun expsSingl e = [e]
  fun expsCons (e, es) = e :: es

  fun identity e = e

  fun fn_ (posl, (_, x), e :@ pos) = 
    Ast.fn_ (x, e :@ pos) @@ mergeAnnotation (SOME posl, pos)

  fun print (posl, e :@ pos) = 
    ML.PRINT (e :@ pos) :@ mergeAnnotation (SOME posl, pos)

  fun app (e1, e2) = APP (e1, e2) :@ posOfTerms [e1, e2]

  fun push (posl, xs : sorted_names, e : exp, posr) =
    Ast.push (List.map (fn ((pos, x), sort) => (x, sort)) xs, e) @@ SOME (Pos.union posl posr)
 
  fun refine (pos1, (pos2, str)) =
    ML.REFINE str :@ SOME (Pos.union pos1 pos2)

  fun quote (pos : pos, rexpr) : src_mlterm =
    ML.QUOTE rexpr :@ mergeAnnotation (SOME pos, RedExpr.getAnnotation rexpr)

  fun exact (pos : pos, e :@ pos') : src_mlterm = 
    ML.EXACT (e :@ pos') :@ mergeAnnotation (SOME pos, pos')

  fun prove (posl, e1, e2, posr) = 
    ML.PROVE (e1, e2) :@ SOME (Pos.union posl posr)

  fun let_ (posl, decls, e, posr) = 
    case decls of 
       [] => e
     | (((_, x), e') :: ds) =>
         Ast.let_ (e', (x, let_ (posl, ds, e, posr))) @@ SOME (Pos.union posl posr)

  fun seqExpSnoc (e, e') = 
    Ast.let_ (e, ("_", e')) @@ posOfTerms [e,e']

  fun seqExpSnocFork (e, es, posr) = 
    ML.SEQ_FORK (e, es) :@ mergeAnnotation (posOfTerms [e], SOME posr)

  fun proj1 pos = 
    ML.FST :@ SOME pos

  fun proj2 pos = 
    ML.SND :@ SOME pos

  fun pair (posl, e1, e2, posr) =
    ML.PAIR (e1, e2) :@ SOME (Pos.union posl posr)

  fun nil_ (posl, posr) = 
    ML.NIL :@ SOME (Pos.union posl posr)

  fun goal pos = 
    ML.GOAL :@ SOME pos

  fun var (pos, x) = 
    ML.VAR x :@ SOME pos

  fun declVal (ident, e) = (ident, e)
  fun declsNil () = []
  fun declsCons (d, ds) = d :: ds

  local
    structure R = RedExpr and O = RedPrlOpData
  in
    fun osortExp () = OSORT O.EXP
    fun osortDim () = PSORT O.DIM

    fun oexpsNil _ = []
    fun oexpsCons (e, es) = e::es

    fun identFromName (pos, x) = (x, SOME pos)
    fun oident (pos, x) = R.IDENT (x, SOME pos)
    fun obinding (posl, xs:names, posr) = R.BINDING (List.map identFromName xs, SOME (Pos.union posl posr))
    fun ogroup (posl, es, posr) = R.GROUP (es, SOME (Pos.union posl posr))
  end

  fun error s = 
    case Stream.front s of
       Stream.Nil => RedPrlError.error [Fpp.text "Syntax error at end of file"]
     | Stream.Cons ((tok, pos), _) =>
       RedPrlError.errorToExn
         (SOME pos,
          RedPrlError.GENERIC
            [Fpp.text "Parse error encountered at token",
             Fpp.text (terminalToString tok)])

end


structure MetalanguageParse = MetalanguageParseFn (structure Streamable = Streamable and Arg = MetalanguageParseAction)