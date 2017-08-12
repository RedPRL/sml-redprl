structure Streamable =
  CoercedStreamable
    (structure Streamable = StreamStreamable
     type 'a item = 'a * Pos.t
     fun coerce (x, _) = x)

structure MetalanguageParseAction = 
struct
  structure ML = MetalanguageSyntax

  fun @@ (f, x) = f x
  infixr @@ 

  type pos = Pos.t
  type pos_string = pos * string

  type string = string
  type oexp = ML.oterm 
  type exp = ML.src_mlterm
  type exps = ML.src_mlterm list
  type names = (pos * string) list


  exception hole
  fun ?e = raise e

  open ML infix :@

  val mergeAnnotation = 
    fn (SOME x, SOME y) => SOME (Pos.union x y)
     | (NONE, SOME x) => SOME x
     | (SOME x, _) => SOME x

  val posOfTerms : exp list -> ML.annotation =
    List.foldl
      (fn (_ :@ ann', ann) => mergeAnnotation (ann', ann))
      NONE

  fun names_nil () = []
  fun names_singl x = [x]
  fun names_cons (x, xs) = x :: xs

  fun exp_nil () = []
  fun exp_singl m = [m]
  fun exp_cons (m, ms) = m :: ms

  fun fn_ (x, m) = 
    ?hole

  fun print m = 
    ?hole

  fun app_exp e = e
  fun app (e1, e2) = APP (e1, e2) :@ posOfTerms [e1, e2]
  fun atm_app e = e

  fun push (posl, xs, e, posr) =
    PUSH (?hole)
      :@ SOME (Pos.union posl posr)

  val fork : exps -> exp = ?hole
  val refine : pos * string -> exp = ?hole
  val quote : oexp -> exp = ?hole
  val exp_atm : exp -> exp = ?hole
  val prove : oexp * exp -> exp = ?hole
  val let_ : (pos * string) * exp * exp -> exp = ?hole
  val proj2 : unit -> exp = ?hole
  val proj1 : unit -> exp = ?hole
  val pair : exp * exp -> exp = ?hole
  val nil_ : unit -> exp = ?hole
  val goal : pos -> exp = ?hole
  val var : pos * string -> exp = ?hole
  val todo : unit -> oexp = ?hole

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
    | TODO

  val error : terminal Streamable.t -> exn = ?hole
end


structure MetalanguageParse = MetalanguageParseFn (structure Streamable = Streamable and Arg = MetalanguageParseAction)