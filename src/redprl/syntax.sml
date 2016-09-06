structure Syntax =
struct
  type symbol = RedPrlAbt.symbol
  type param = RedPrlAbt.param

  datatype 'a view =
     AX
   | BOOL | TT | FF
   | S1 | BASE | LOOP of param

  local
    open RedPrlAbt
    structure O = RedPrlOpData
    infix $ $$ \
  in
    val into =
      fn AX => O.MONO O.AX $$ []
       | BOOL => O.MONO O.BOOL $$ []
       | TT => O.MONO O.TRUE $$ []
       | FF => O.MONO O.FALSE $$ []
       | S1 => O.MONO O.S1 $$ []
       | BASE => O.MONO O.BASE $$ []
       | LOOP r => O.POLY (O.LOOP r) $$ []
  end
end
