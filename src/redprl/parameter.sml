structure RedPrlParamData =
struct
  datatype param_sort =
     DIM
   | EXN
   | LBL
   | OPID
   | HYP
   | LVL

  datatype 'a param_operator =
     DIM0
   | DIM1
   | LVL_SUCC of 'a
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
     | LVL => "lvl"
end

structure RedPrlParameter : ABT_PARAMETER =
struct
  open RedPrlParamData
  type 'a t = 'a param_operator

  fun map f =
    fn DIM0 => DIM0
     | DIM1 => DIM1
     | LVL_SUCC a => LVL_SUCC (f a)

  structure Sort = RedPrlParamSort

  val arity =
    fn DIM0 => (DIM0, DIM)
     | DIM1 => (DIM1, DIM)
     | LVL_SUCC a => (LVL_SUCC LVL, LVL)

  fun eq f =
    fn (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | (LVL_SUCC a, LVL_SUCC b) => f (a, b)
     | _ => false

  fun toString f =
    fn DIM0 => "dim0"
     | DIM1 => "dim1"
     | LVL_SUCC a => f a ^ "'"

  fun join zer mul =
    fn DIM0 => zer
     | DIM1 => zer
     | LVL_SUCC l => mul (l, zer)
end

structure RedPrlParameterTerm = AbtParameterTerm (RedPrlParameter)
