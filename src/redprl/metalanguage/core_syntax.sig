structure CoreSyntaxData = 
struct
  type 'a row = (string * 'a) list

  datatype vtype = 
     UNIT
   | TENSOR of vtype row
   | DOWN of ctype
   | PROOF
   | OEXP

  and ctype = 
     UP of vtype 
   | AND of ctype row
   | ARR of vtype * ctype

  structure Var = AbtSymbol ()

  datatype vterm =
     VAR of Var.t

  and cterm = 
     RET of vterm
   | LET of cterm * Var.t * cterm 
end