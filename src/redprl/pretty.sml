structure PP = PrettyPrint (AnsiColors)

structure TermPrinter :
sig
  include SHOW 
  val paramToString : Sym.t RedPrlParameterTerm.t -> string
end =
struct
  structure Abt = RedPrlAbt
  structure ShowVar = Abt.Var
  structure ShowSym = Abt.Sym
  structure O = RedPrlOpData
  structure P = RedPrlParameterTerm

  structure UP = UnparseAbt (structure Abt = Abt and Unparse = Unparse)

  open Abt O Unparse

  type t = abt

  fun @@ (f, x) = f x
  infix 0 @@ $ $$ \

  val paramToString = P.toString ShowSym.toString

  fun notation m =
    case Abt.out m of
      (* , x *)
      POLY (HYP_REF x) $ [] => SOME o atom @@ "," ^ ShowVar.toString x
    | (* (x : A) -> B *)
      MONO DFUN $ [_ \ a, (_, [x]) \ bx] =>
        let
          val left = "(" ^ ShowVar.toString x ^ " : " ^ toString a ^ ")"
        in
          SOME @@ infix' (Right, 3, "->") (atom left, unparse bx)
        end
    | (* M N *)
      MONO AP $ [_ \ m, _ \ n] =>
        SOME @@ adj (unparse m, unparse n)
    | (* (x : A) * B *)
      MONO DPROD $ [_ \ a, (_, [x]) \ bx] =>
        let
          val left = "(" ^ ShowVar.toString x ^ " : " ^ toString a ^ ")"
        in
          SOME @@ infix' (Right, 3, "*") (atom left, unparse bx)
        end
    | (* <M, N> *)
      MONO PAIR $ [_ \ m, _ \ n] =>
        SOME o atom @@ "<" ^ toString m ^ ", " ^ toString n ^ ">"
    | (* <x> A *)
      MONO ID_ABS $ [(([x], []) \ a)] =>
        SOME o atom @@ "<" ^ ShowVar.toString x  ^ "> " ^ toString a
    | (* loop[p] *)
      POLY (LOOP p) $ [] =>
        SOME o atom @@ "loop[" ^ paramToString p ^ "]"
    | (* A @ p *)
      POLY (ID_AP p) $ [_ \ a] =>
        SOME @@ infix' (Left, 5, "@") (unparse a, atom (paramToString p))
    | _ => NONE

  and unparse m = UP.unparse notation m
  and toString m =
      parens (done (unparse m))
end
