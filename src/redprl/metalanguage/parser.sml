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
    | IN of pos
    | DOUBLE_RIGHT_ARROW of pos
    | LSQUARE of pos
    | RSQUARE of pos
    | LPAREN of pos
    | RPAREN of pos
    | COMMA of pos
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
    | BOOL of pos

  val terminalToString = 
    fn LET _ => "LET"
     | FN _ => "FN"
     | IN _ => "IN"
     | DOUBLE_RIGHT_ARROW _ => "DOUBLE_RIGHT_ARROW"
     | LSQUARE _ => "LSQUARE"
     | RSQUARE _ => "RSQUARE"
     | LPAREN _ => "LPAREN"
     | RPAREN _ => "RPAREN"
     | COMMA _ => "COMMA"
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
     | BOOL _ => "BOOL"


end

structure MetalanguageParseAction = 
struct
  structure ML = MetalanguageSyntax
  open ML infix :@
  open MetalanguageTerminal

  type string = string
  type oexp = RedPrlAst.ast * ML.osort 
  type exp = ML.src_mlterm
  type exps = ML.src_mlterm list
  type names = (pos * string) list

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

  fun names_nil () = []
  fun names_singl x = [x]
  fun names_cons (x, xs) = x :: xs

  fun exp_nil () = []
  fun exp_singl e = [e]
  fun exp_cons (e, es) = e :: es

  fun fn_ (posl, (_, x), e :@ pos) = 
    Ast.fn_ (x, e :@ pos) @@ mergeAnnotation (SOME posl, pos)

  fun print (posl, e :@ pos) = 
    ML.PRINT (e :@ pos) :@ mergeAnnotation (SOME posl, pos)

  fun app_exp e = e
  fun app (e1, e2) = APP (e1, e2) :@ posOfTerms [e1, e2]
  fun atm_app e = e

  fun push (posl, xs : names, e : exp, posr) =
    Ast.push (List.map #2 xs, e) @@ SOME (Pos.union posl posr)

  fun fork (posl, es, posr) =
    ML.EACH es :@ SOME (Pos.union posl posr)
 
  fun refine (pos1, (pos2, str)) =
    ML.REFINE str :@ SOME (Pos.union pos1 pos2)

  fun quote (pos : pos, (oexp, osort)) : src_mlterm =
    ML.QUOTE (oexp, osort) :@ mergeAnnotation (SOME pos, RedPrlAst.getAnnotation oexp)

  fun exp_atm e = e

  fun prove (posl, e1, e2, posr) = 
    ML.PROVE (e1, e2) :@ SOME (Pos.union posl posr)

  fun let_ (posl, (_, x), e, ex, posr) =
    Ast.let_ (e, (x, ex)) @@ SOME (Pos.union posl posr)

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

  local
    open RedPrlAst
    structure O = RedPrlOpData
    infixr 3 $$
  in
    fun obool pos = 
      (annotate pos @@ O.MONO O.BOOL $$ [], O.EXP)
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