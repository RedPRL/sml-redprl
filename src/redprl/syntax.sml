structure Syntax =
struct
  structure Tm = RedPrlAbt
  type variable = Tm.variable
  type symbol = Tm.symbol
  type param = Tm.param
  type sort = Tm.sort

  type equation = param * param
  type dir = param * param

  datatype 'a view =
     VAR of variable * sort
   (* axiom *)
   | AX
   (* week bool: true, false and if *)
   | BOOL | TT | FF | IF of (variable * 'a) * 'a * ('a * 'a)
   (* strict bool: strict if (true and false are shared) *)
   | S_BOOL | S_IF of 'a * ('a * 'a)
   (* circle: base, loop and s1_elim *)
   | S1 | BASE | LOOP of param | S1_ELIM of (variable * 'a) * 'a * ('a * (symbol * 'a))
   (* function: lambda and app *)
   | DFUN of 'a * variable * 'a | LAM of variable * 'a | AP of 'a * 'a
   (* prodcut: pair, fst and snd *)
   | DPROD of 'a * variable * 'a | PAIR of 'a * 'a | FST of 'a | SND of 'a
   (* path: path abstraction and path application *)
   | PATH_TY of (symbol * 'a) * 'a * 'a | PATH_ABS of symbol * 'a | PATH_AP of 'a * param
   (* hcom *)
   | HCOM of {dir: dir, class: 'a, cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* it is a "view" for custom operators *)
   | CUST
   (* meta *)
   | META

  local
    open Tm
    structure O = RedPrlOpData and P = RedPrlParameterTerm and E = RedPrlError
    infix $ $$ $# \
  in
    val into =
      fn VAR (x, tau) => check (`x, tau)
       | AX => O.MONO O.AX $$ []

       | BOOL => O.MONO O.BOOL $$ []
       | TT => O.MONO O.TRUE $$ []
       | FF => O.MONO O.FALSE $$ []
       | IF ((x, cx), m, (t, f)) => O.MONO O.IF $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ t, ([],[]) \ f]

       | S_BOOL => O.MONO O.S_BOOL $$ []
       | S_IF (m, (t, f)) => O.MONO O.S_IF $$ [([],[]) \ m, ([],[]) \ t, ([],[]) \ f]

       | S1 => O.MONO O.S1 $$ []
       | BASE => O.MONO O.BASE $$ []
       | LOOP r => O.POLY (O.LOOP r) $$ []
       | S1_ELIM ((x, cx), m, (b, (u, l))) => O.MONO O.S1_ELIM $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ b, ([u],[]) \ l]

       | DFUN (a, x, bx) => O.MONO O.DFUN $$ [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) => O.MONO O.LAM $$ [([],[x]) \ mx]
       | AP (m, n) => O.MONO O.AP $$ [([],[]) \ m, ([],[]) \ n]

       | DPROD (a, x, bx) => O.MONO O.DPROD $$ [([],[]) \ a, ([],[x]) \ bx]
       | PAIR (m, n) => O.MONO O.PAIR $$ [([],[]) \ m, ([],[]) \ n]
       | FST m => O.MONO O.FST $$ [([],[]) \ m]
       | SND m => O.MONO O.SND $$ [([],[]) \ m]

       | PATH_TY ((u, a), m, n) => O.MONO O.PATH_TY $$ [([u],[]) \ a, ([],[]) \ m, ([],[]) \ n]
       | PATH_ABS (u, m) => O.MONO O.PATH_ABS $$ [([u],[]) \ m]
       | PATH_AP (m, r) => O.POLY (O.PATH_AP r) $$ [([],[]) \ m]

       | HCOM {dir, class=ty, cap, tubes} =>
           let
             val (eqs, tubes) = ListPair.unzip tubes
             val tubes' = List.map (fn (d, t) => ([d], []) \ t) tubes
           in
             O.POLY (O.HCOM (O.TAG_NONE, eqs, dir)) $$
               (([],[]) \ ty) :: (([],[]) \ cap) :: tubes'
           end
       | CUST => raise Fail "CUST"
       | META => raise Fail "META"

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)
       | O.MONO O.AX $ _ => AX
       | O.MONO O.BOOL $ _ => BOOL
       | O.MONO O.TRUE $ _ => TT
       | O.MONO O.FALSE $ _ => FF
       | O.MONO O.IF $ [(_,[x]) \ cx, _ \ m, _ \ t, _ \ f] => IF ((x, cx), m, (t, f))

       | O.MONO O.S_BOOL $ _ => S_BOOL
       | O.MONO O.S_IF $ [_ \ m, _ \ t, _ \ f] => S_IF (m, (t, f))

       | O.MONO O.S1 $ _ => S1
       | O.MONO O.BASE $ _ => BASE
       | O.POLY (O.LOOP r) $ _ => LOOP r
       | O.MONO O.S1_ELIM $ [(_,[x]) \ cx, _ \ m, _ \ b, ([u],_) \ l] => S1_ELIM ((x, cx), m, (b, (u, l)))

       | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] => DFUN (a, x, bx)
       | O.MONO O.LAM $ [(_,[x]) \ mx] => LAM (x, mx)
       | O.MONO O.AP $ [_ \ m, _ \ n] => AP (m, n)

       | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] => DPROD (a, x, bx)
       | O.MONO O.PAIR $ [_ \ m, _ \ n] => PAIR (m, n)
       | O.MONO O.FST $ [_ \ m] => FST m
       | O.MONO O.SND $ [_ \ m] => SND m

       | O.MONO O.PATH_TY $ [([u],_) \ a, _ \ m, _ \ n] => PATH_TY ((u, a), m, n)
       | O.MONO O.PATH_ABS $ [([u],_) \ m] => PATH_ABS (u, m)
       | O.POLY (O.PATH_AP r) $ [_ \ m] => PATH_AP (m, r)

       | O.POLY (O.HCOM (tag, eqs, dir)) $ args =>
         let
           val (ty, args) =
             case (tag, args) of
                (O.TAG_NONE, ((_ \ ty) :: args)) => (ty, args)
              | (O.TAG_BOOL, args) => (O.MONO O.BOOL $$ [], args)
              | (O.TAG_S1, args) => (O.MONO O.S1 $$ [], args)
              | (O.TAG_DFUN, (A :: xB :: args)) => (O.MONO O.DFUN $$ [A, xB], args)
              | (O.TAG_DPROD, (A :: xB :: args)) => (O.MONO O.DPROD $$ [A, xB], args)
              | (O.TAG_PATH, (uA :: a0 :: a1 :: args)) => (O.MONO O.PATH_TY $$ [uA, a0, a1], args)
              | _ => raise Fail "Syntax.out hcom: Malformed tag"
           val (_ \ cap) :: args = args
           fun goTube (([d], []) \ tube) = (d, tube)
             | goTube _ = raise Fail "Syntax.out hcom: Malformed tube"
           val tubes = List.map goTube args
         in
           HCOM {dir=dir, class=ty, cap=cap, tubes=ListPair.zipEq(eqs, tubes)}
         end

       | O.POLY (O.CUST _) $ _ => CUST
       | _ $# _ => META
       | _ => raise E.error [E.% "Syntax view encountered unrecognized term", E.! m]

    fun heteroCom (eqs, dir) ((u, a), cap, tube) =
      let
        val (r, r') = dir
        fun coe v m = O.POLY (O.COE (O.TAG_NONE, dir)) $$ [([u],[]) \ a, ([],[]) \ m]
        val ty = ([],[]) \ substSymbol (r', u) a
        val cap' = ([],[]) \ coe r cap
        val tube' = List.map (fn ([v],_) \ n => ([v],[]) \ coe (P.ret v) n | _ => raise Fail "malformed tube") tube
      in
        O.POLY (O.HCOM (O.TAG_NONE, eqs, dir)) $$ ty :: cap' :: tube'
      end
  end
end
