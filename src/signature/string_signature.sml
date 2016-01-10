structure StringSignature : STRING_SIGNATURE =
struct
  type opid = string
  structure Telescope = StringTelescope

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

  type decl = (def, tac, thm) StringSignatureDecl.decl

  (* A signature / [sign] is a telescope of declarations. *)
  type sign = decl StringTelescope.telescope
end
