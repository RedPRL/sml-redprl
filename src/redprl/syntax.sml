structure Syntax =
struct
  structure Tm = RedPrlAbt
  structure K = RedPrlKind
  structure L = RedPrlLevel
  type variable = Tm.variable
  type symbol = Tm.symbol
  type param = Tm.param
  type sort = Tm.sort
  type kind = K.t

  type equation = param * param
  type dir = param * param

  type label = string
  structure Fields =
  struct
    val empty = []

    exception Absent
    fun lookup lbl fields =
      case List.find (fn (lbl', _) => lbl' = lbl) fields of
        SOME (_, tm) => tm
      | NONE => raise Absent

    fun remove lbl = List.filter (fn (lbl', _) => lbl' <> lbl)

    fun update (lbl, tm) fields = remove lbl fields @ [(lbl, tm)]
  end

  datatype 'a view =
     VAR of variable * sort
   (* the trivial realizer of sort TRIV for judgments lacking interesting
    * computational content. *)
   | TV
   (* the trivial realizer of sort EXP for types lacking interesting
    * computational content. This is the "ax(iom)" in Nuprl. *)
   | AX
   (* formal composition *)
   | FCOM of {dir: dir, cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* strict bool *)
   | BOOL | TT | FF | IF of 'a * ('a * 'a)
   (* weak bool *)
   | WBOOL | WIF of (variable * 'a) * 'a * ('a * 'a)
   (* natural numbers *)
   | NAT | ZERO | SUCC of 'a
   | NAT_REC of 'a * ('a * (variable * variable * 'a))
   (* integers, reusing natural numbers *)
   | INT | NEGSUCC of 'a
   | INT_REC of 'a * ('a * (variable * variable * 'a) * 'a * (variable * variable * 'a))
   (* empty type *)
   | VOID
   (* circle *)
   | S1 | BASE | LOOP of param | S1_REC of (variable * 'a) * 'a * ('a * (symbol * 'a))
   (* function: lambda and app *)
   | DFUN of 'a * variable * 'a | LAM of variable * 'a | APP of 'a * 'a
   (* record *)
   | RECORD of ((string * variable) * 'a) list
   | TUPLE of (label * 'a) list | PROJ of string * 'a | TUPLE_UPDATE of (string * 'a) * 'a
   (* path: path abstraction and path application *)
   | PATH_TY of (symbol * 'a) * 'a * 'a | PATH_ABS of symbol * 'a | PATH_APP of 'a * param
   (* equality *)
   | EQUALITY of 'a * 'a * 'a
   (* fcom types *)
   | BOX of {dir: dir, cap: 'a, boundaries: (equation * 'a) list}
   | CAP of {dir: dir, tubes: (equation * (symbol * 'a)) list, coercee: 'a}
   (* universes *)
   | UNIVERSE of L.level * kind
   (* hcom operator *)
   | HCOM of {dir: dir, ty: 'a, cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* coe operator *)
   | COE of {dir: dir, ty: (symbol * 'a), coercee: 'a}
   (* com operator *)
   | COM of {dir: dir, ty: (symbol * 'a), cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* custom operators *)
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
        val tubes = List.map (fn (d, t) => ([d],[]) \ t) tubes
      in
        (eqs, tubes)
      end

    fun outTubes (eqs, tubes) =
      let
        fun goTube (([d],_) \ tube) = (d, tube)
          | goTube _ = raise E.error [Fpp.text "Syntax.outTubes: Malformed tube"]
      in
        ListPair.zipEq (eqs, List.map goTube tubes)
      end

    fun intoFcom {dir, cap, tubes} =
      let val (eqs, tubes) = intoTubes tubes
      in O.POLY (O.FCOM (dir, eqs)) $$ (([],[]) \ cap) :: tubes
      end

    fun intoHcom {dir, ty, cap, tubes} =
      let val (eqs, tubes) = intoTubes tubes
      in O.POLY (O.HCOM (dir, eqs)) $$ (([],[]) \ ty) :: (([],[]) \ cap) :: tubes
      end

    fun intoCom {dir, ty=(u,a), cap, tubes} =
      let val (eqs, tubes) = intoTubes tubes
      in O.POLY (O.COM (dir, eqs)) $$ (([u],[]) \ a) :: (([],[]) \ cap) :: tubes
      end

    fun outRecordFields (lbls, args) =
      let
        val init = {rcd = [], vars = []}
        val {rcd, ...} = 
          ListPair.foldlEq
            (fn (lbl, (_, xs) \ ty, {rcd, vars}) =>
              let
                val ren = ListPair.foldlEq (fn (x, var, ren) => Var.Ctx.insert ren x var) Var.Ctx.empty (xs, vars)
                val ty' = Tm.renameVars ren ty
                val var = Var.named lbl
              in
                {rcd = ((lbl, var), ty') :: rcd,
                 vars = vars @ [var]}
              end)
            init
            (lbls, args)
      in
        List.rev rcd
      end

    fun intoBoundaries boundaries =
      let
        val (eqs, boundaries) = ListPair.unzip boundaries
        val boundaries = List.map (fn b => ([], []) \ b) boundaries
      in
        (eqs, boundaries)
      end

    fun outBoudaries (eqs, boundaries) =
      ListPair.zipEq (eqs, List.map (fn (_ \ b) => b) boundaries)

    fun intoBox {dir, cap, boundaries} =
      let val (eqs, boundaries) = intoBoundaries boundaries
      in O.POLY (O.BOX (dir, eqs)) $$ (([],[]) \ cap) :: boundaries
      end

    (* note that the coercee goes first! *)
    fun intoCap {dir, tubes, coercee} =
      let val (eqs, tubes) = intoTubes tubes
      in O.POLY (O.CAP (dir, eqs)) $$ (([],[]) \ coercee) :: tubes
      end
  in
    fun intoTupleFields fs =
      let
        val (lbls, tms) = ListPair.unzip fs
        val tms = List.map (fn tm => ([],[]) \ tm) tms
      in
        (lbls, tms)
      end

    fun outTupleFields (lbls, args) =
      ListPair.mapEq (fn (lbl, (_ \ tm)) => (lbl, tm)) (lbls, args)

    val into =
      fn VAR (x, tau) => check (`x, tau)

       | TV => O.MONO O.TV $$ []
       | AX => O.MONO O.AX $$ []

       | FCOM args => intoFcom args

       | BOOL => O.MONO O.BOOL $$ []
       | TT => O.MONO O.TT $$ []
       | FF => O.MONO O.FF $$ []
       | IF (m, (t, f)) => O.MONO O.IF $$ [([],[]) \ m, ([],[]) \ t, ([],[]) \ f]

       | WBOOL => O.MONO O.WBOOL $$ []
       | WIF ((x, cx), m, (t, f)) => O.MONO O.WIF $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ t, ([],[]) \ f]

       | NAT => O.MONO O.NAT $$ []
       | ZERO => O.MONO O.ZERO $$ []
       | SUCC m => O.MONO O.SUCC $$ [([],[]) \ m]
       | NAT_REC (m, (n, (a, b, p))) => O.MONO O.NAT_REC $$ [([],[]) \ m, ([],[]) \ n, ([],[a,b]) \ p]

       | INT => O.MONO O.INT $$ []
       | NEGSUCC m => O.MONO O.NEGSUCC $$ [([],[]) \ m]
       | INT_REC (m, (n, (a, b, p), q, (c, d, r))) =>
           O.MONO O.INT_REC $$ [([],[]) \ m, ([],[]) \ n, ([],[a,b]) \ p, ([],[]) \ q, ([],[c,d]) \ r]

       | VOID => O.MONO O.VOID $$ []

       | S1 => O.MONO O.S1 $$ []
       | BASE => O.MONO O.BASE $$ []
       | LOOP r => O.POLY (O.LOOP r) $$ []
       | S1_REC ((x, cx), m, (b, (u, l))) => O.MONO O.S1_REC $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ b, ([u],[]) \ l]

       | DFUN (a, x, bx) => O.MONO O.DFUN $$ [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) => O.MONO O.LAM $$ [([],[x]) \ mx]
       | APP (m, n) => O.MONO O.APP $$ [([],[]) \ m, ([],[]) \ n]

       | RECORD fields =>
            let
             val init = {labels = [], args = [], vars = []}
             val {labels, args, ...} =
               List.foldl
                 (fn (((lbl, var), ty), {labels, args, vars}) =>
                     {labels = lbl :: labels,
                      vars = vars @ [var],
                      args = (([],vars) \ ty) :: args})
                 init
                 fields
           in
             O.MONO (O.RECORD (List.rev labels)) $$ List.rev args
           end
       | TUPLE fs =>
           let
             val (lbls, tys) = intoTupleFields fs
           in
             O.MONO (O.TUPLE lbls) $$ tys
           end
       | PROJ (lbl, a) => O.MONO (O.PROJ lbl) $$ [([],[]) \ a]
       | TUPLE_UPDATE ((lbl, n), m) => O.MONO (O.TUPLE_UPDATE lbl) $$ [([],[]) \ n, ([],[]) \ m]

       | PATH_TY ((u, a), m, n) => O.MONO O.PATH_TY $$ [([u],[]) \ a, ([],[]) \ m, ([],[]) \ n]
       | PATH_ABS (u, m) => O.MONO O.PATH_ABS $$ [([u],[]) \ m]
       | PATH_APP (m, r) => O.POLY (O.PATH_APP r) $$ [([],[]) \ m]

       | EQUALITY (a, m, n) => O.MONO O.EQUALITY $$ [([],[]) \ a, ([],[]) \ m, ([],[]) \ n]

       | BOX args => intoBox args
       | CAP args => intoCap args

       | UNIVERSE (l, k) => O.POLY (O.UNIVERSE (L.into l, k)) $$ []

       | HCOM args => intoHcom args
       | COE {dir, ty = (u, a), coercee} =>
           O.POLY (O.COE dir) $$ [([u],[]) \ a, ([],[]) \ coercee]
       | COM args => intoCom args

       | CUST => raise Fail "CUST"
       | META => raise Fail "META"

    val intoAp = into o APP
    val intoLam = into o LAM

    fun intoCoe dir (ty, m) =
      into (COE {dir = dir, ty = ty, coercee = m})

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)

       | O.MONO O.TV $ _ => TV
       | O.MONO O.AX $ _ => AX

       | O.POLY (O.FCOM (dir, eqs)) $ (_ \ cap) :: tubes =>
           FCOM {dir = dir, cap = cap, tubes = outTubes (eqs, tubes)}

       | O.MONO O.BOOL $ _ => BOOL
       | O.MONO O.TT $ _ => TT
       | O.MONO O.FF $ _ => FF
       | O.MONO O.IF $ [_ \ m, _ \ t, _ \ f] => IF (m, (t, f))

       | O.MONO O.WBOOL $ _ => WBOOL
       | O.MONO O.WIF $ [(_,[x]) \ cx, _ \ m, _ \ t, _ \ f] => WIF ((x, cx), m, (t, f))

       | O.MONO O.NAT $ _ => NAT
       | O.MONO O.ZERO $ _ => ZERO
       | O.MONO O.SUCC $ [_ \ m] => SUCC m
       | O.MONO O.NAT_REC $ [_ \ m, _ \ n, (_,[a,b]) \ p] => NAT_REC (m, (n, (a, b, p)))

       | O.MONO O.INT $ _ => INT
       | O.MONO O.NEGSUCC $ [_ \ m] => NEGSUCC m
       | O.MONO O.INT_REC $ [_ \ m, _ \ n, (_,[a,b]) \ p, _ \ q, (_,[c,d]) \ r] =>
           INT_REC (m, (n, (a, b, p), q, (c, d, r)))

       | O.MONO O.VOID $ _ => VOID

       | O.MONO O.S1 $ _ => S1
       | O.MONO O.BASE $ _ => BASE
       | O.POLY (O.LOOP r) $ _ => LOOP r
       | O.MONO O.S1_REC $ [(_,[x]) \ cx, _ \ m, _ \ b, ([u],_) \ l] => S1_REC ((x, cx), m, (b, (u, l)))

       | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] => DFUN (a, x, bx)
       | O.MONO O.LAM $ [(_,[x]) \ mx] => LAM (x, mx)
       | O.MONO O.APP $ [_ \ m, _ \ n] => APP (m, n)

       | O.MONO (O.RECORD lbls) $ tms => RECORD (outRecordFields (lbls, tms)) 
       | O.MONO (O.TUPLE lbls) $ tms => TUPLE (outTupleFields (lbls, tms))
       | O.MONO (O.PROJ lbl) $ [_ \ m] => PROJ (lbl, m)
       | O.MONO (O.TUPLE_UPDATE lbl) $ [_ \ n, _ \ m] => TUPLE_UPDATE ((lbl, n), m)

       | O.MONO O.PATH_TY $ [([u],_) \ a, _ \ m, _ \ n] => PATH_TY ((u, a), m, n)
       | O.MONO O.PATH_ABS $ [([u],_) \ m] => PATH_ABS (u, m)
       | O.POLY (O.PATH_APP r) $ [_ \ m] => PATH_APP (m, r)

       | O.MONO O.EQUALITY $ [_ \ a, _ \ m, _ \ n] => EQUALITY (a, m, n)

       | O.POLY (O.BOX (dir, eqs)) $ (_ \ cap) :: boundaries =>
           BOX {dir = dir, cap = cap, boundaries = outBoudaries (eqs, boundaries)}
       (* note that the coercee goes first! *)
       | O.POLY (O.CAP (dir, eqs)) $ (_ \ coercee) :: tubes =>
           CAP {dir = dir, tubes = outTubes (eqs, tubes), coercee = coercee}

       | O.POLY (O.UNIVERSE (l, k)) $ _ => UNIVERSE (L.out l, k)

       | O.POLY (O.HCOM (dir, eqs)) $ (_ \ ty) :: (_ \ cap) :: tubes =>
           HCOM {dir = dir, ty = ty, cap = cap, tubes = outTubes (eqs, tubes)}
       | O.POLY (O.COE dir) $ [([u],_) \ a, _ \ m] =>
           COE {dir = dir, ty = (u, a), coercee = m}

       | O.POLY (O.CUST _) $ _ => CUST
       | _ $# _ => META
       | _ => raise E.error [Fpp.text "Syntax view encountered unrecognized term", TermPrinter.ppTerm m]
  end
end
