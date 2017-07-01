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
   (* the trivial realizer for equality, which is called 'axiom' in NuPRL. *)
   | AX
   (* formal composition *)
   | FCOM of {dir: dir, cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* weak bool: true, false and if *)
   | BOOL | TT | FF | IF of (variable * 'a) * 'a * ('a * 'a)
   (* strict bool: strict if (true and false are shared) *)
   | S_BOOL | S_IF of 'a * ('a * 'a)
   (* int *)
   | INT | NUMBER of param
   (* nat, reusing the number *)
   | NAT
   (* empty type *)
   | VOID
   (* circle: base, loop and s1_elim *)
   | S1 | BASE | LOOP of param | S1_ELIM of (variable * 'a) * 'a * ('a * (symbol * 'a))
   (* function: lambda and app *)
   | DFUN of 'a * variable * 'a | LAM of variable * 'a | AP of 'a * 'a
   (* prodcut: pair, fst and snd *)
   | DPROD of 'a * variable * 'a | PAIR of 'a * 'a | FST of 'a | SND of 'a
   (* path: path abstraction and path application *)
   | PATH_TY of (symbol * 'a) * 'a * 'a | PATH_ABS of symbol * 'a | PATH_AP of 'a * param
   (* hcom operator *)
   | HCOM of {dir: dir, ty: 'a, cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* coe operator *)
   | COE of {dir: dir, ty: (symbol * 'a), coercee: 'a}
   (* com operator *)
   | COM of {dir: dir, ty: (symbol * 'a), cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* it is a "view" for custom operators *)
   | CUST
   (* meta *)
   | META

  local
    open Tm
    structure O = RedPrlOpData and P = RedPrlParameterTerm and E = RedPrlError
    infix $ $$ $# \

    fun intoTubes tubes =
      let
        val (eqs, tubes) = ListPair.unzip tubes
        val tubes = List.map (fn (d, t) => ([d], []) \ t) tubes
      in
        (eqs, tubes)
      end
    fun outTubes (eqs, tubes) =
      let
        fun goTube (([d], []) \ tube) = (d, tube)
          | goTube _ = raise Fail "Syntax.outTubes: Malformed tube"
      in
        ListPair.zipEq (eqs, List.map goTube tubes)
      end
  in
    fun intoFcom' (dir, eqs) args = O.POLY (O.FCOM (dir, eqs)) $$ args

    fun intoFcom (dir, eqs) (cap, tubes) =
      intoFcom' (dir, eqs) ((([],[]) \ cap) :: tubes)

    fun intoHcom' (dir, eqs) (ty, args) =
      O.POLY (O.HCOM (dir, eqs)) $$ (([],[]) \ ty) :: args

    fun intoHcom (dir, eqs) (ty, cap, tubes) =
      intoHcom' (dir, eqs) (ty, (([],[]) \ cap) :: tubes)

    fun intoCom' (dir, eqs) ((u, a), args) =
      O.POLY (O.COM (dir, eqs)) $$ (([u],[]) \ a) :: args

    fun intoCom (dir, eqs) (ty, cap, tubes) =
      intoCom' (dir, eqs) (ty, (([],[]) \ cap) :: tubes)

    val into =
      fn VAR (x, tau) => check (`x, tau)
       | AX => O.MONO O.AX $$ []

       | FCOM {dir, cap, tubes} =>
           let
             val (eqs, tubes) = intoTubes tubes
           in
             intoFcom (dir, eqs) (cap, tubes)
           end

       | BOOL => O.MONO O.BOOL $$ []
       | TT => O.MONO O.TRUE $$ []
       | FF => O.MONO O.FALSE $$ []
       | IF ((x, cx), m, (t, f)) => O.MONO O.IF $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ t, ([],[]) \ f]

       | S_BOOL => O.MONO O.S_BOOL $$ []
       | S_IF (m, (t, f)) => O.MONO O.S_IF $$ [([],[]) \ m, ([],[]) \ t, ([],[]) \ f]

       | INT => O.MONO O.INT $$ []
       | NUMBER n => O.POLY (O.NUMBER n) $$ []

       | NAT => O.MONO O.NAT $$ []

       | VOID => O.MONO O.VOID $$ []

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

       | HCOM {dir, ty, cap, tubes} =>
           let
             val (eqs, tubes) = intoTubes tubes
           in
             intoHcom (dir, eqs) (ty, cap, tubes)
           end
       | COE {dir, ty = (u, a), coercee} =>
           O.POLY (O.COE dir) $$ [([u],[]) \ a, ([],[]) \ coercee]
       | COM {dir, ty = (u, a), cap, tubes} =>
           let
             val (eqs, tubes) = intoTubes tubes
           in
             intoCom (dir, eqs) ((u, a), cap, tubes)
           end

       | CUST => raise Fail "CUST"
       | META => raise Fail "META"

    val intoAp = into o AP
    val intoLam = into o LAM

    val intoFst = into o FST
    val intoSnd = into o SND
    val intoPair = into o PAIR

    fun intoCoe dir (ty, m) =
      into (COE {dir = dir, ty = ty, coercee = m})

    fun intoCom (dir as (r, r'), eqs) ((u, a), cap, tubes) =
      let
        fun coe v m = intoCoe (v, r') ((u, a), m)
        fun goTube (([v],_) \ n) = ([v],[]) \ coe (P.ret v) n
          | goTube _ = raise Fail "malformed tube"
      in
        intoHcom (dir, eqs) (substSymbol (r', u) a, coe r cap, List.map goTube tubes)
      end

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)
       | O.MONO O.AX $ _ => AX

       | O.POLY (O.FCOM (dir, eqs)) $ (_ \ cap) :: tubes =>
           FCOM {dir = dir, cap = cap, tubes = outTubes (eqs, tubes)}

       | O.MONO O.BOOL $ _ => BOOL
       | O.MONO O.TRUE $ _ => TT
       | O.MONO O.FALSE $ _ => FF
       | O.MONO O.IF $ [(_,[x]) \ cx, _ \ m, _ \ t, _ \ f] => IF ((x, cx), m, (t, f))

       | O.MONO O.S_BOOL $ _ => S_BOOL
       | O.MONO O.S_IF $ [_ \ m, _ \ t, _ \ f] => S_IF (m, (t, f))

       | O.MONO O.INT $ _ => INT
       | O.POLY (O.NUMBER n) $ _ => NUMBER n

       | O.MONO O.NAT $ _ => NAT

       | O.MONO O.VOID $ _ => VOID

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

       | O.POLY (O.HCOM (dir, eqs)) $ (_ \ ty) :: (_ \ cap) :: tubes =>
           HCOM {dir = dir, ty = ty, cap = cap, tubes = outTubes (eqs, tubes)}
       | O.POLY (O.COE dir) $ [([u],_) \ a, _ \ m] =>
           COE {dir = dir, ty = (u, a), coercee = m}

       | O.POLY (O.CUST _) $ _ => CUST
       | _ $# _ => META
       | _ => raise E.error [Fpp.text "Syntax view encountered unrecognized term", TermPrinter.ppTerm m]
  end
end
