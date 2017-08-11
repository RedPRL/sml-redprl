structure MetalanguageParseAction = 
struct
  structure ML = MetalanguageSyntax

  structure R = 
  struct
    (* TODO *)
    type resolver_state = {}
    type 'a m = resolver_state -> 'a
    fun ret a _ = a
    fun map f m s = f (m s)
    fun bind (m : 'a m) (f : 'a -> 'b m) : 'b m = fn s => f (m s) s
  end

  fun @@ (f, x) = f x
  infixr @@ 

  fun >>= (m, f) = R.bind m f
  infix >>=

  type string = string
  type oexp = ML.oterm R.m
  type exp = ML.mlterm_ R.m
  type exps = ML.mlterm_ R.m list
  type names = string list

  exception hole
  fun ?e = raise e

  fun names_nil () = []
  fun names_singl x = [x]
  fun names_cons (x, xs) = x :: xs

  fun exp_nil () = []
  fun exp_singl m = [m]
  fun exp_cons (m, ms) = m :: ms

  fun fn_ (x, m) = 
    R.map ML.FUN @@
      ?hole

  val fn_ : string * exp -> exp = ?hole
  val print : exp -> exp = ?hole
  val app_exp : exp -> exp = ?hole
  val app : exp * exp -> exp = ?hole
  val atm_app : exp -> exp = ?hole
  val push : names * exp -> exp = ?hole
  val fork : exps -> exp = ?hole
  val refine : string -> exp = ?hole
  val quote : oexp -> exp = ?hole
  val exp_atm : exp -> exp = ?hole
  val prove : oexp * exp -> exp = ?hole
  val let_ : string * exp * exp -> exp = ?hole
  val proj2 : unit -> exp = ?hole
  val proj1 : unit -> exp = ?hole
  val pair : exp * exp -> exp = ?hole
  val nil_ : unit -> exp = ?hole
  val goal : unit -> exp = ?hole
  val var : string -> exp = ?hole
  val todo : unit -> oexp = ?hole

  datatype terminal =
      LET
    | FN
    | IN
    | DOUBLE_RIGHT_ARROW
    | LSQUARE
    | RSQUARE
    | LPAREN
    | RPAREN
    | COMMA
    | EQUALS
    | BEGIN
    | END
    | IDENT of string
    | PROVE
    | PROJ1
    | PROJ2
    | BACKTICK
    | REFINE
    | GOAL
    | PUSH
    | PRINT
    | TODO

  structure Streamable = StreamStreamable
  val error : terminal Streamable.t -> exn = ?hole
end

structure MetalanguageParse = MetalanguageParseFn (structure Streamable = StreamStreamable and Arg = MetalanguageParseAction)