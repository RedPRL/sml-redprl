structure RedPrlSyntax =
struct

  structure O = RedPrlOperator
  structure RS = SortData

  datatype 'a view =
     CAPPROX of RS.sort * 'a * 'a
   | CEQUIV of RS.sort * 'a * 'a
   | BASE of RS.sort
   | TOP of RS.sort
   | UNIV of RS.sort * 'a
   | AX
   | DFUN of 'a * variable * 'a
   | FUN of 'a * 'a
   | NOT of 'a
   | LAM of variable * 'a
   | AP of 'a * 'a
   | DFUN_DOM of 'a
   | DFUN_COD of 'a * 'a
   | VOID

   | ATOM of RS.sort
   | TOKEN of symbol * RS.sort
   | IF_EQ of RS.sort * RS.sort * 'a * 'a * 'a * 'a

   | RCD_CONS of symbol * 'a * 'a
   | RCD_SINGL of symbol * 'a
   | RECORD_TY of symbol * 'a * variable * 'a
   | RCD_PROJ of symbol * 'a
   | RCD_PROJ_TY of symbol * 'a * 'a

   | BOOL
   | BOOL_TT
   | BOOL_FF
   | BOOL_IF of (variable * 'a) * 'a * 'a * 'a

   | REFINE_SCRIPT of RS.sort * 'a * 'a * 'a
   | EXTRACT_WITNESS of RS.sort * 'a
   | STR_LITERAL of string

   | TAC_SEQ of 'a * (symbol * RS.sort) list * 'a
   | TAC_ORELSE of 'a * 'a
   | MTAC_ALL of 'a
   | MTAC_EACH of 'a list
   | MTAC_FOCUS of int * 'a
   | TAC_PROGRESS of 'a
   | TAC_REC of variable * 'a
   | TAC_INTRO of int option
   | TAC_EQ of int option
   | TAC_EXT
   | TAC_CUM
   | TAC_CHKINF
   | TAC_ELIM of symbol * RS.sort
   | TAC_ETA of symbol * RS.sort
   | TAC_HYP of symbol * RS.sort
   | TAC_UNHIDE of symbol * RS.sort
   | TAC_AUTO
   | TAC_ID
   | TAC_FAIL
   | TAC_TRACE of RS.sort * 'a
   | TAC_CSTEP of int
   | TAC_CEVAL
   | TAC_CSYM
   | TAC_REWRITE_GOAL of RS.sort * 'a
   | TAC_EVAL_GOAL of symbol option
   | TAC_NORMALIZE of symbol option
   | TAC_WITNESS of RS.sort * 'a
   | TAC_UNFOLD of symbol * symbol option
   | HYP_REF of symbol

  datatype 'a open_view =
      APP of 'a view
    | VAR of variable
    | MVAR of metavariable * (symbol * sort) list * 'a list

  infix 3 $ $$ $#
  infix 2 \
end

structure RedPrlAbtSyntax =
struct
  local
    structure Syn = RedPrlSyntax (AbtSyntaxView (RedPrlAbt))
    structure UnparseAbt = UnparseAbt (structure Abt = RedPrlAbt and Unparse = Unparse)
    open Unparse
    open Syn

    fun @@ (f, x) = f x
    infixr 0 @@

    fun var (x, tau) =
      RedPrlAbt.check (`x, RedPrlOperator.S.EXP tau)

    fun unparse m =
      UnparseAbt.unparse (fn n => SOME (inner n) handle _ => NONE) m

    and inner m =
      case out m of
         MEMBER (_, m, a) => infix' (Non, 0, "\226\136\136") (unparse m, unparse a)
       | EQ (_, m, n, a) => atom @@ toString m ^ " = "  ^ toString n ^ " \226\136\136 " ^ toString a
       | CEQUIV (_, m, n) => infix' (Non, 0, "~") (unparse m, unparse n)
       | AX => atom "Ax"
       | RCD_CONS (lbl, a, b) => infix' (Right, 5, "\226\136\183") (infix' (Non, 5, "=") (atom (Symbol.toString lbl), unparse a), unparse b)
       | RCD_PROJ (lbl, m) => postfix (4, ". " ^ Symbol.toString lbl) (unparse m)
       | RECORD_TY (lbl, a, x, bx) =>
           let
             val lblVar = Variable.named (Symbol.toString lbl)
             val b' = RedPrlAbt.subst (var (lblVar, SortData.EXP), x) bx
             val decl = infix' (Non, 0, ":") (atom (Symbol.toString lbl), unparse a)
             val rcd = infix' (Left, 0, ",") (decl, unparse b')
           in
             atom @@ "{" ^ parens (done rcd) ^ "}"
           end
       | UNIV (_, lvl) => atom @@ "\240\157\149\140{" ^ toString lvl ^ "}"
       | LBASE => atom "0"
       | LSUCC l => adj (atom "s", unparse l)
       | FUN (a, b) => infix' (Right, 7, "\226\134\146") (unparse a, unparse b)
       | DFUN (a, x, bx) =>
           let
             val dom = infix' (Non, 0, ":") (atom (Variable.toString x), unparse a)
             val dom' = atom @@ "(" ^ parens (done dom) ^ ")"
             val cod = unparse bx
           in
             infix' (Right, 7, "\226\134\146") (dom', cod)
           end
       | ATOM _ => atom "atom"
       | TOKEN (u, _) => atom @@ "'" ^ Symbol.toString u
       | TOP _ => atom @@ "\226\138\164"
       | AP (m, n) => adj (unparse m, unparse n)
       | LAM (x, mx) => prefix (0, "\206\187" ^ Variable.toString x ^ ".") (unparse mx)
       | BASE _ => atom "Base"
       | FRESH (_, _, u, m) => prefix (0, "\206\189" ^ Symbol.toString u ^ ".") (unparse m)
       | RAISE e => atom @@ "throw(" ^ toString e ^ ")"
       | TRY (a, m, x, nx) => atom @@ "try[" ^ Symbol.toString a ^ "](" ^ toString m ^ ") with " ^ Variable.toString x ^ "." ^ toString nx
       | IF_EQ (_, _, t1, t2, l, r) =>
           atom
             @@ "if "
              ^ toString t1
              ^ " = "
              ^ toString t2
              ^ " then "
              ^ toString l
              ^ " else "
              ^ toString r
       | MTAC_ALL m => unparse m
       | MTAC_EACH ts => atom @@ "[" ^ ListSpine.pretty toString "," ts ^ "]"
       | MTAC_FOCUS (i, t) => atom @@ "#" ^ Int.toString i ^ " {" ^ toString t ^ "}"
       | TAC_SEQ (t1, bindings, t2) =>
           let
             val us = "[" ^ List.foldl (fn ((u, _), s) => Symbol.toString u ^ (if s = "" then "" else ", ") ^ s) "" bindings ^ "]"
             val t1' =
               case bindings of
                  [] => unparse t1
                 | _ => infix' (Right, 7, "\226\134\144") (atom us, unparse t1)
           in
             infix' (Left, 7, ";") (t1', unparse t2)
           end
       | REFINE_SCRIPT (_, goal, script, extract) =>
           atom
             @@ "refine ["
              ^ toString goal
              ^ "] with ["
              ^ toString script
              ^ "] ~> ["
              ^ (case out extract of OPT_SOME (_, m) => toString m | _ => toString extract)
              ^ "]"
       | TAC_CEVAL => atom "ceval"
       | TAC_CSYM => atom "csym"
       | TAC_WITNESS (_, m) => atom @@ "witness [" ^ toString m ^ "]"
       | TAC_CHKINF => atom "chkinf"
       | OPT_SOME (_, m) => atom @@ "some(" ^ toString m ^ ")"
       | OPT_NONE _ => atom "none"
       | _ => raise Match

    and toString m = parens (done (unparse m))
  in
    open Syn
    val toString = toString
    val var = var
end
