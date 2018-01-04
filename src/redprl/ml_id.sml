structure MlId :> ML_ID = 
struct
  datatype t = CONST of string | VAR of int * string option

  val eq : t * t -> bool = op=

  val compare = 
    fn (CONST s1, CONST s2) => String.compare (s1, s2)
     | (VAR (i1, _), VAR (i2, _)) => Int.compare (i1, i2)
     | (CONST _, VAR _) => LESS
     | _ => GREATER

  val counter = ref 0
  
  fun new () = 
    (counter := !counter + 1;
     VAR (!counter, NONE))
  
  fun const a = CONST a

  fun fresh str = 
    (counter := !counter + 1;
     VAR (!counter, SOME str))

  val toString = 
    fn CONST str => str
     | VAR (i, NONE) => "$" ^ Int.toString i
     | VAR (_, SOME str) => str
end
