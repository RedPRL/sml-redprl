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
   | BOOL | TT | FF | IF of (variable * 'a) * 'a * ('a * 'a)
   | S1 | BASE | LOOP of param
   | DFUN of 'a * variable * 'a | LAM of variable * 'a
   | ID_TY of (symbol * 'a) * 'a * 'a | ID_ABS of symbol * 'a | ID_AP of 'a * param

  local
    open Tm
    structure O = RedPrlOpData and P = RedPrlParameterTerm
    infix $ $$ \
  in
    val into =
      fn VAR (x, tau) => check (`x, tau)
       | AX => O.MONO O.AX $$ []
       | BOOL => O.MONO O.BOOL $$ []
       | TT => O.MONO O.TRUE $$ []
       | FF => O.MONO O.FALSE $$ []
       | IF ((x, cx), m, (t, f)) => O.MONO O.IF $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ t, ([],[]) \ f]
       | S1 => O.MONO O.S1 $$ []
       | BASE => O.MONO O.BASE $$ []
       | LOOP r => O.POLY (O.LOOP r) $$ []
       | DFUN (a, x, bx) => O.MONO O.DFUN $$ [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) => O.MONO O.LAM $$ [([],[x]) \ mx]
       | ID_TY ((u, a), m, n) => O.MONO O.ID_TY $$ [([u],[]) \ a, ([],[]) \ m, ([],[]) \ n]
       | ID_ABS (u, m) => O.MONO O.ID_ABS $$ [([u],[]) \ m]
       | ID_AP (m, r) => O.POLY (O.ID_AP r) $$ [([],[]) \ m]

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)
       | O.MONO O.AX $ _ => AX
       | O.MONO O.BOOL $ _ => BOOL
       | O.MONO O.TRUE $ _ => TT
       | O.MONO O.FALSE $ _ => FF
       | O.MONO O.IF $ [(_,[x]) \ cx, _ \ m, _ \ t, _ \ f] => IF ((x, cx), m, (t, f))
       | O.MONO O.S1 $ _ => S1
       | O.MONO O.BASE $ _ => BASE
       | O.POLY (O.LOOP r) $ _ => LOOP r
       | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] => DFUN (a, x, bx)
       | O.MONO O.LAM $ [(_,[x]) \ mx] => LAM (x, mx)
       | O.MONO O.ID_TY $ [([u],_) \ a, _ \ m, _ \ n] => ID_TY ((u, a), m, n)
       | O.MONO O.ID_ABS $ [([u],_) \ m] => ID_ABS (u, m)
       | O.POLY (O.ID_AP r) $ [_ \ m] => ID_AP (m, r)
       | _ => raise Match

    fun heteroCom (exts, dir) ((u, a), cap, tube) =
      let
        val (r, r') = dir
        fun coe v m = O.POLY (O.COE (O.TAG_NONE, dir)) $$ [([u],[]) \ a, ([],[]) \ m]
        val ty = ([],[]) \ substSymbol (r', u) a
        val cap' = ([],[]) \ coe r cap
        val tube' = List.map (fn ([v],_) \ n => ([v],[]) \ coe (P.ret v) n | _ => raise Fail "malformed tube") tube
      in
        O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) $$ ty :: cap' :: tube'
      end
  end
end
