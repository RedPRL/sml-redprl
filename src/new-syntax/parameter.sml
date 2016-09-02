structure RedPrlParamData =
struct
  datatype param_sort =
     DIM
   | EXN
   | LBL
   | OPID
   | HYP

  datatype 'a param_operator =
     DIM0
   | DIM1
end

structure RedPrlParamSort : ABT_SORT =
struct
  open RedPrlParamData

  type t = param_sort
  val eq : t * t -> bool = op=

  val toString =
    fn DIM => "dim"
     | EXN => "exn"
     | LBL => "lbl"
     | OPID => "opid"
     | HYP => "hyp"
end

structure RedPrlParameter : ABT_PARAMETER =
struct
  open RedPrlParamData
  type 'a t = 'a param_operator

  fun map f =
    fn DIM0 => DIM0
     | DIM1 => DIM1

  structure Sort = RedPrlParamSort

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

structure RedPrlParameterTerm = AbtParameterTerm (RedPrlParameter)
