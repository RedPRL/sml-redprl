signature REDEXPR = 
sig
  type annotation

  type 'a ident = 'a * annotation

  datatype 'a expr = 
     IDENT of 'a ident
   | NUMERAL of int
   | BINDING of 'a ident list * annotation
   | TYPED_BINDING of 'a ident list * 'a expr * annotation
   | GROUP of 'a expr list * annotation

  type 'a forest = 'a expr list

  type abt
  type state

  val reader : state -> string expr -> abt
end