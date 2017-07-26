structure Syntax =
struct
  structure Tm = RedPrlAbt
  type variable = Tm.variable
  type symbol = Tm.symbol
  type param = Tm.param
  type sort = Tm.sort

  type equation = param * param
  type dir = param * param

  type label = string
  structure LabelDict = SplayDict (structure Key = StringOrdered)

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
   | INT_REC of 'a * ((variable * variable * 'a) * 'a * (variable * variable * 'a))
   (* empty type *)
   | VOID
   (* circle *)
   | S1 | BASE | LOOP of param | S1_REC of (variable * 'a) * 'a * ('a * (symbol * 'a))
   (* function: lambda and app *)
   | DFUN of 'a * variable * 'a | LAM of variable * 'a | APP of 'a * 'a
   (* product: pair, fst and snd *)
   | DPROD of 'a * variable * 'a | PAIR of 'a * 'a | FST of 'a | SND of 'a
   (* record *)
   | RECORD of ((string * variable) * 'a) list
   | TUPLE of 'a LabelDict.dict | PROJ of string * 'a | TUPLE_UPDATE of (string * 'a) * 'a
   (* path: path abstraction and path application *)
   | PATH_TY of (symbol * 'a) * 'a * 'a | PATH_ABS of symbol * 'a | PATH_APP of 'a * param
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
        val tubes = List.map (fn (d, t) => ([d], []) \ t) tubes
      in
        (eqs, tubes)
      end

    fun outTubes (eqs, tubes) =
      let
        fun goTube (([d], []) \ tube) = (d, tube)
          | goTube _ = raise E.error [Fpp.text "Syntax.outTubes: Malformed tube"]
      in
        ListPair.zipEq (eqs, List.map goTube tubes)
      end

  in
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

    fun intoTupleFields fs =
      let
        val (lbls, tms) = ListPair.unzip (LabelDict.toList fs)
        val tms = List.map (fn tm => ([],[]) \ tm) tms
      in
        (lbls, tms)
      end

    fun outTupleFields (lbls, args) =
      ListPair.foldrEq
        (fn (lbl, (_ \ tm), m) =>
          case LabelDict.insert' m lbl tm of
            (_ , true) => raise E.error [Fpp.text "Duplicate labels"]
          | (dict, _) => dict)
        LabelDict.empty (lbls, args)


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

       | TV => O.MONO O.TV $$ []
       | AX => O.MONO O.AX $$ []

       | FCOM {dir, cap, tubes} =>
           let
             val (eqs, tubes) = intoTubes tubes
           in
             intoFcom (dir, eqs) (cap, tubes)
           end

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
       | INT_REC (m, ((a, b, p), q, (c, d, r))) =>
           O.MONO O.INT_REC $$ [([],[]) \ m, ([],[a,b]) \ p, ([],[]) \ q, ([],[c,d]) \ r]

       | VOID => O.MONO O.VOID $$ []

       | S1 => O.MONO O.S1 $$ []
       | BASE => O.MONO O.BASE $$ []
       | LOOP r => O.POLY (O.LOOP r) $$ []
       | S1_REC ((x, cx), m, (b, (u, l))) => O.MONO O.S1_REC $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ b, ([u],[]) \ l]

       | DFUN (a, x, bx) => O.MONO O.DFUN $$ [([],[]) \ a, ([],[x]) \ bx]
       | LAM (x, mx) => O.MONO O.LAM $$ [([],[x]) \ mx]
       | APP (m, n) => O.MONO O.APP $$ [([],[]) \ m, ([],[]) \ n]

       | DPROD (a, x, bx) => O.MONO O.DPROD $$ [([],[]) \ a, ([],[x]) \ bx]
       | PAIR (m, n) => O.MONO O.PAIR $$ [([],[]) \ m, ([],[]) \ n]
       | FST m => O.MONO O.FST $$ [([],[]) \ m]
       | SND m => O.MONO O.SND $$ [([],[]) \ m]

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

    val intoAp = into o APP
    val intoLam = into o LAM

    val intoFst = into o FST
    val intoSnd = into o SND
    val intoPair = into o PAIR

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
       | O.MONO O.INT_REC $ [_ \ m, (_,[a,b]) \ p, _ \ q, (_,[c,d]) \ r] =>
           INT_REC (m, ((a, b, p), q, (c, d, r)))

       | O.MONO O.VOID $ _ => VOID

       | O.MONO O.S1 $ _ => S1
       | O.MONO O.BASE $ _ => BASE
       | O.POLY (O.LOOP r) $ _ => LOOP r
       | O.MONO O.S1_REC $ [(_,[x]) \ cx, _ \ m, _ \ b, ([u],_) \ l] => S1_REC ((x, cx), m, (b, (u, l)))

       | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] => DFUN (a, x, bx)
       | O.MONO O.LAM $ [(_,[x]) \ mx] => LAM (x, mx)
       | O.MONO O.APP $ [_ \ m, _ \ n] => APP (m, n)

       | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] => DPROD (a, x, bx)
       | O.MONO O.PAIR $ [_ \ m, _ \ n] => PAIR (m, n)
       | O.MONO O.FST $ [_ \ m] => FST m
       | O.MONO O.SND $ [_ \ m] => SND m

       | O.MONO (O.RECORD lbls) $ tms => RECORD (outRecordFields (lbls, tms)) 
       | O.MONO (O.TUPLE lbls) $ tms => TUPLE (outTupleFields (lbls, tms))
       | O.MONO (O.PROJ lbl) $ [_ \ m] => PROJ (lbl, m)
       | O.MONO (O.TUPLE_UPDATE lbl) $ [_ \ n, _ \ m] => TUPLE_UPDATE ((lbl, n), m)

       | O.MONO O.PATH_TY $ [([u],_) \ a, _ \ m, _ \ n] => PATH_TY ((u, a), m, n)
       | O.MONO O.PATH_ABS $ [([u],_) \ m] => PATH_ABS (u, m)
       | O.POLY (O.PATH_APP r) $ [_ \ m] => PATH_APP (m, r)

       | O.POLY (O.HCOM (dir, eqs)) $ (_ \ ty) :: (_ \ cap) :: tubes =>
           HCOM {dir = dir, ty = ty, cap = cap, tubes = outTubes (eqs, tubes)}
       | O.POLY (O.COE dir) $ [([u],_) \ a, _ \ m] =>
           COE {dir = dir, ty = (u, a), coercee = m}

       | O.POLY (O.CUST _) $ _ => CUST
       | _ $# _ => META
       | _ => raise E.error [Fpp.text "Syntax view encountered unrecognized term", TermPrinter.ppTerm m]
  end
end
