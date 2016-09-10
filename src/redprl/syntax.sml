structure Syntax =
struct
  structure Tm = RedPrlAbt
  type variable = Tm.variable
  type symbol = Tm.symbol
  type param = Tm.param
  type sort = Tm.sort

  datatype 'a view =
     VAR of variable * sort
   | AX
   | BOOL | TT | FF
   | S1 | BASE | LOOP of param
   | DFUN of 'a * variable * 'a | LAM of variable * 'a

  local
    open Tm
    structure O = RedPrlOpData
    infix $ $$ \
  in
    val into =
      fn VAR (x, tau) => check (`x, tau)
       | AX => O.MONO O.AX $$ []
       | BOOL => O.MONO O.BOOL $$ []
       | TT => O.MONO O.TRUE $$ []
       | FF => O.MONO O.FALSE $$ []
       | S1 => O.MONO O.S1 $$ []
       | BASE => O.MONO O.BASE $$ []
       | LOOP r => O.POLY (O.LOOP r) $$ []
       | DFUN (a, x, bx) => O.MONO O.DFUN $$ [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) => O.MONO O.LAM $$ [([],[x]) \ mx]

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)
       | O.MONO O.AX $ _ => AX
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
