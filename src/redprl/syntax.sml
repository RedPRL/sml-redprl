structure Syntax =
struct
  type variable = RedPrlAbt.variable
  type symbol = RedPrlAbt.symbol
  type param = RedPrlAbt.param

  datatype 'a view =
     AX
   | BOOL | TT | FF
   | S1 | BASE | LOOP of param
   | DFUN of 'a * variable * 'a | LAM of variable * 'a

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
       | DFUN (a, x, bx) => O.MONO O.DFUN $$ [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) => O.MONO O.LAM $$ [([],[x]) \ mx]

    fun out m =
      case RedPrlAbt.out m of
         O.MONO O.AX $ _ => AX
       | O.MONO O.BOOL $ _ => BOOL
       | O.MONO O.TRUE $ _ => TT
       | O.MONO O.FALSE $ _ => FF
       | O.MONO O.S1 $ _ => S1
       | O.MONO O.BASE $ _ => BASE
       | O.POLY (O.LOOP r) $ _ => LOOP r
       | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] => DFUN (a, x, bx)
       | O.MONO O.LAM $ [(_,[x]) \ mx] => LAM (x, mx)
       | _ => raise Match
  end
end
