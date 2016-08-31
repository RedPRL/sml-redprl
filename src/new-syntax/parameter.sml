structure Param =
struct
  datatype sort =
     DIM
   | EXN
   | LBL

  datatype 'a operator =
     DIM0
   | DIM1
end

structure ParamAbtSort : ABT_SORT =
struct
  open Param

  type t = sort
  val eq : t * t -> bool = op=

  val toString =
    fn DIM => "dim"
     | EXN => "exn"
     | LBL => "lbl"
end

structure AbtParameter : ABT_PARAMETER =
struct
  open Param
  type 'a t = 'a operator

  fun map f =
    fn DIM0 => DIM0
     | DIM1 => DIM1

  structure Sort = ParamAbtSort

  val arity =
    fn DIM0 => (DIM0, DIM)
     | DIM1 => (DIM1, DIM)

  fun eq f =
    fn (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn DIM0 => "dim0"
     | DIM1 => "dim1"

  fun join zer mul =
    fn DIM0 => zer
     | DIM1 => zer
end

structure AbtParameterTerm = AbtParameterTerm (AbtParameter)
