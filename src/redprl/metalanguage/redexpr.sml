structure RedExpr =
struct
  type atom = string

  type 'a eqn = {lhs : 'a, rhs : 'a}

  datatype 'a con =
     ATOM of atom
   | LIST of 'a list
   | BIND_CELL of atom list   
   | TYPED_CELL of atom list * 'a
   | LABEL_CELL of string * 'a
   | TUBE_CELL of 'a eqn * string * 'a

  type 'a info = {pos : Pos.t option, con : 'a}
  datatype node = NODE of node con info

  fun makeNode (left, right, con) = 
    NODE {pos = SOME (Pos.pos left right), con = con}
end
