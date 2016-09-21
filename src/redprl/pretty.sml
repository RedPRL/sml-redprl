structure PP = PrettyPrint (AnsiColors)

structure TermPrinter = 
struct
  structure Abt = RedPrlAbt
  structure O = RedPrlOperator

  structure UP = UnparseAbt (structure Abt = Abt and Unparse = Unparse)

  open Abt O Unparse

  fun @@ (f, x) = f x
  infix 0 @@

  fun notation m = 
    case Abt.out m of
      `x => SOME (atom "i am a variable!")
    | _ => NONE

  and toString m =
    parens (done (UP.unparse notation m))
end