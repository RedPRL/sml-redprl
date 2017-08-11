structure Streamable =
  CoercedStreamable
    (structure Streamable = StreamStreamable
     type 'a item = 'a * Pos.t
     fun coerce (x, _) = x)

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
    ?hole

  fun print m = 
    ?hole
    (* R.map ML.PRINT m *)

  fun app_exp m = m
  fun app (m1 : exp, m2 : exp) : exp = ?hole
    (* m1 >>= (fn x1 => m2 >>= (fn x2 => R.ret (?hole))) *)

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

  val error : terminal Streamable.t -> exn = ?hole
end


structure MetalanguageParse = MetalanguageParseFn (structure Streamable = Streamable and Arg = MetalanguageParseAction)