structure StringSignatureDecl =
struct
  datatype ('def, 'tac, 'thm) decl =
      DEF of 'def
    | TAC of 'tac
    | THM of 'thm
end

(* The first stage of signature elaboration contains three kinds of declaration:
 * definitions, tactics and theorems. Parsing of terms and expressions is
 * deferred to the next stage of signature elaboration, [AST_SIGNATURE]. *)
signature STRING_SIGNATURE =
sig
  type term = string
  type goal = string
  type symbol = string
  type sort = string
  type metavariable = string
  type valence = sort list * sort list * sort

  type symbols = (symbol * sort) list
  type arguments = (metavariable * valence) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  type tac =
    {parameters : symbols,
     arguments : arguments,
     script : term}

  type thm =
    {parameters : symbols,
     arguments : arguments,
     goal : term,
     script : term}

  include SIGNATURE
    where type decl = (def, tac, thm) StringSignatureDecl.decl
end
