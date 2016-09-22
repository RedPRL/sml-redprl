structure PP = PrettyPrint (AnsiColors)

structure TermPrinter = 
struct
  structure Abt = RedPrlAbt
  structure ShowVar = Abt.Var
  structure O = RedPrlOpData

  structure UP = UnparseAbt (structure Abt = Abt and Unparse = Unparse)

  open Abt O Unparse

  fun @@ (f, x) = f x
  infix 0 @@ $ $$ \

  fun notation m = 
    case Abt.out m of
      (* A -> B *)
      MONO DFUN $ [_ \ a, (_, []) \ bx] =>
        SOME (atom @@ toString a ^ " -> " ^ toString bx)
    | (* (x : A) -> B *)
      MONO DFUN $ [_ \ a, (_, [x]) \ bx] =>
        SOME (atom @@ "(" ^ ShowVar.toString x ^ ":" ^ toString a ^ ") -> " ^ toString bx)
    | _ => NONE

  and toString m =
      parens (done (UP.unparse notation m))
end
