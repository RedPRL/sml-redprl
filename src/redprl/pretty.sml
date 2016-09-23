structure PP = PrettyPrint (AnsiColors)

structure TermPrinter = 
struct
  structure Abt = RedPrlAbt
  structure ShowVar = Abt.Var
  structure ShowSym = Abt.Sym
  structure O = RedPrlOpData
  structure P = RedPrlParameterTerm

  structure UP = UnparseAbt (structure Abt = Abt and Unparse = Unparse)

  open Abt O Unparse

  fun @@ (f, x) = f x
  infix 0 @@ $ $$ \

  val paramToString = P.toString ShowSym.toString

  fun notation m = 
    case Abt.out m of
      (* , x *)
      POLY (HYP_REF x) $ [] => SOME (atom @@ ", " ^ ShowVar.toString x)
    | (* A -> B *)
      MONO FUN $ [_ \ a, (_, []) \ b] =>
        SOME (infix' (Right, 3, "->") (unparse a, unparse b))
    | (* (x : A) -> B *)
      MONO DFUN $ [_ \ a, (_, [x]) \ bx] =>
        let
          val left = "(" ^ ShowVar.toString x ^ " : " ^ toString a ^ ")"
        in
          SOME (infix' (Right, 3, "->") (atom left, unparse bx))
        end
    | (* < x > A *)
      MONO ID_ABS $ [(([x], []) \ a)] =>
        SOME (atom @@ "< " ^ ShowVar.toString x  ^ " > " ^ toString a)
    | (* univ [ p ] *)
      POLY (UNIV p) $ [] =>
        SOME (atom @@ "univ [ " ^ paramToString p ^ " ]")
    | (* loop [ p ] *)
      POLY (LOOP p) $ [] =>
        SOME (atom @@ "loop [ " ^ paramToString p ^ " ]")
    | (* A @ p *)
      POLY (ID_AP p) $ [(([],[]) \ a)] =>
        SOME (infix' (Left, 5, "@") (unparse a, atom (paramToString p)))
    | _ => NONE

  and unparse m = UP.unparse notation m
  and toString m =
      parens (done (unparse m))
end
