signature ML_SYNTAX =
sig
  type id
  type metavariable
  type jdg
  type term
  type vty

  type metas = (metavariable * Tm.valence) list

  (* TODO: add algebraic effects and handlers *)

  datatype value =
     (* thunk N *)
     THUNK of cmd

     (* x *)
   | VAR of id

     (* () *)
   | NIL

     (* [V1].V2 *)
   | ABS of value * value

     (* [X : v...] *)
   | METAS of metas
  
     (* 'e *)
   | TERM of term

  and cmd =
     (* let x = M in N *)
     BIND of cmd * id * cmd
     
     (* ret V *)
   | RET of value

     (* force V *)
   | FORCE of value

     (* fn x:A => N *)
   | FN of id * vty * cmd

     (* N(V) *)
   | AP of cmd * value
  
     (* print V *)
   | PRINT of Pos.t option * value

     (* refine J e *)
   | REFINE of string option * jdg * term

     (* fresh [X:v...] *)
   | FRESH of (string option * Tm.valence) list

     (* pm V as X... in N *)
   | MATCH_METAS of value * metavariable list * cmd

     (* pm V as [Ψ].x in N *)
   | MATCH_ABS of value * id * id * cmd

     (* pm V as (x, y) in N *)
   | MATCH_THM of value * id * id * cmd

     (* abort *)
   | ABORT

  (* ν [X : v...] in N *)
  val nu : metas * cmd -> cmd

  (* some macros *)
  val termAbs : metas * term -> cmd
  val theoremAbs : string option * metas * jdg * term -> cmd
  val printExtractAbs : Pos.t option * value -> cmd

  (* TODO:

  val ppVal : value -> Fpp.doc
  val ppCmd : cmd -> Fpp.doc

  *)
end
