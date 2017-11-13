structure SyntaxData = 
struct
  structure Var = AbtSymbol ()
  structure Row = StringListDict

  type 'a row = 'a Row.dict
  type 'a con = string * 'a

  datatype vtype = 
     TENSOR of vtype row
   | PLUS of vtype row
   | DOWN of ctype
   | PROOF
   | OEXP
   | META

  and ctype = 
     UP of vtype 
   | OBJ of ctype row
   | ARR of vtype * ctype

  (* internal language *)
  structure I = 
  struct
    datatype eff = 
       EVAR of Var.t
       (* builtin effects *)
     | MATCH of string * ctype

    datatype vpat = 
       PTUPLE of vpat row
     | PCON of vpat row
     | PVAR of Var.t

    datatype vterm =
       VNEU of vneu
     | TUPLE of vterm row
     | CON of vterm con
     | THUNK of cterm

    and vneu = 
       VAR of Var.t
     | VTERM of vterm * vtype

   and cterm = 
      CNEU of cneu
    | FUN of vpat * cterm
    | RECORD of cterm row
    | LET of vpat * cneu * cterm
    | RET of vterm
    | FORCE of vneu
  
   and cneu =
      PROJ of cneu * string
    | APP of cneu * vterm
    | CTERM of cterm * ctype
  end

  (* external language *)
  structure E = 
  struct
    type var = string
    datatype pat = 
       PVAR of string
     | PRCD of (string * pat) list
     | PCON of string * pat

    datatype term =
       VAR of string
     | LET of decl list * term
     | RCD of (string * term) list
     | FUN of branch list
     | CON of string * term

    and branch = BRANCH of pat * term
    and decl = DECL of pat * term * term
  end
end