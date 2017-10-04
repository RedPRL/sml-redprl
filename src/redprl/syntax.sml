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

  type equation = Tm.abt * Tm.abt
  type dir = Tm.abt * Tm.abt
  type 'a tube = equation * (variable * 'a)

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
   | FCOM of {dir: dir, cap: 'a, tubes: 'a tube list}
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
   | S1 | BASE | LOOP of 'a | S1_REC of (variable * 'a) * 'a * ('a * (symbol * 'a))
   (* function: lambda and app *)
   | FUN of 'a * variable * 'a | LAM of variable * 'a | APP of 'a * 'a
   (* record *)
   | RECORD of ((string * variable) * 'a) list
   | TUPLE of (label * 'a) list | PROJ of string * 'a | TUPLE_UPDATE of (string * 'a) * 'a
   (* path: path abstraction and path application *)
   | PATH_TY of (symbol * 'a) * 'a * 'a | PATH_ABS of symbol * 'a | PATH_APP of 'a * 'a
   (* equality *)
   | EQUALITY of 'a * 'a * 'a
   (* fcom types *)
   | BOX of {dir: dir, cap: 'a, boundaries: (equation * 'a) list}
   | CAP of {dir: dir, tubes: (equation * (symbol * 'a)) list, coercee: 'a}
   (* V *)
   | V of 'a * 'a * 'a * 'a
   | VIN of 'a * 'a * 'a | VPROJ of 'a * 'a * 'a
   (* universes *)
   | UNIVERSE of L.level * kind
   (* hcom operator *)
   | HCOM of {dir: dir, ty: 'a, cap: 'a, tubes: (equation * (symbol * 'a)) list}
   (* coe operator *)
   | COE of {dir: dir, ty: (symbol * 'a), coercee: 'a}
   (* com operator *)
   | COM of {dir: dir, ty: (symbol * 'a), cap: 'a, tubes: (equation * (symbol * 'a)) list}

   | DIM0 | DIM1

   (* custom operators *)
   | CUST
   (* meta *)
   | META of Tm.metavariable * sort



  local
    open Tm
    structure O = RedPrlOpData and E = RedPrlError
    infix $ $$ $# \
  in
    fun outVec' (f : abt -> 'a) (vec : abt) : 'a list =
      let
        val O.MONO (O.MK_VEC _) $ args = Tm.out vec
      in
        List.map (fn _ \ t => f t) args
      end

    val outVec = outVec' (fn x => x)

    fun unpackAny m =
      let
        val O.MONO (O.MK_ANY _) $ [_ \ m'] = Tm.out m
      in
        m'
      end

    fun outSelector (s : abt) : Tm.variable O.selector = 
      case Tm.out s of 
         O.MONO O.SEL_GOAL $ _ => O.IN_GOAL
       | O.MONO O.SEL_HYP $ [_ \ e] =>
         (case Tm.out (unpackAny e) of
             `x => O.IN_HYP x
           | _ => raise Fail "Invalid selector")

    fun outTube tube = 
      let
        val O.MONO O.MK_TUBE $ [_ \ r1, _ \ r2, (_,[u]) \ mu] = Tm.out tube
      in
        ((r1, r2), (u, mu))
      end

    fun outBoundary boundary = 
      let
        val O.MONO O.MK_BOUNDARY $ [_ \ r1, _ \ r2, _ \ m] = Tm.out boundary
      in
        ((r1, r2), m)
      end

    (* TODO: use outVec' *)
    fun outTubes system =
      let
        val O.MONO (O.MK_VEC _) $ args = Tm.out system
      in
        List.map (fn _ \ t => outTube t) args
      end

    fun outBoundaries boundaries =
      let
        val O.MONO (O.MK_VEC _) $ args = Tm.out boundaries
      in
        List.map (fn _ \ b => outBoundary b) args
      end

    fun intoTube ((r1, r2), (u, e)) = 
      O.MONO O.MK_TUBE $$ 
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([],[u]) \ e]

    fun intoBoundary ((r1, r2), e) = 
      O.MONO O.MK_BOUNDARY $$ 
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([],[]) \ e]


    fun intoTubes tubes = 
      let
        val n = List.length tubes
      in
        O.MONO (O.MK_VEC (O.TUBE, n)) $$
          List.map (fn t => ([],[]) \ intoTube t) tubes
      end

    fun intoBoundaries boundaries = 
      let
        val n = List.length boundaries
      in
        O.MONO (O.MK_VEC (O.BOUNDARY, n)) $$
          List.map (fn b => ([],[]) \ intoBoundary b) boundaries
      end
  end

  local
    open Tm
    structure O = RedPrlOpData and E = RedPrlError
    infix $ $$ $# \


    fun intoFcom {dir = (r1, r2), cap, tubes} =
      O.MONO O.FCOM $$
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([],[]) \ cap,
         ([],[]) \ intoTubes tubes]

    fun intoHcom {dir = (r1, r2), ty, cap, tubes} =
      O.MONO O.HCOM $$ 
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([],[]) \ ty,
         ([],[]) \ cap,
         ([],[]) \ intoTubes tubes]

    fun intoCom {dir = (r1, r2), ty=(u,a), cap, tubes} =
      O.MONO O.COM $$ 
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([],[u]) \ a,
         ([],[]) \ cap,
         ([],[]) \ intoTubes tubes]


    (* fun outBoudaries (eqs, boundaries) =
      ListPair.zipEq (eqs, List.map (fn (_ \ b) => b) boundaries) *)

    fun intoBox {dir = (r1, r2), cap, boundaries} =
      O.MONO O.BOX $$ 
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([],[]) \ cap,
         ([],[]) \ intoBoundaries boundaries]

    fun intoCap {dir = (r1, r2), coercee, tubes} =
      O.MONO O.CAP $$ 
        [([],[]) \ r1,
         ([],[]) \ r2,
         ([], []) \ coercee,
         ([],[]) \ intoTubes tubes]

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
       | LOOP r => O.MONO O.LOOP $$ [([],[]) \ r]
       | S1_REC ((x, cx), m, (b, (u, l))) => O.MONO O.S1_REC $$ [([],[x]) \ cx, ([],[]) \ m, ([],[]) \ b, ([],[u]) \ l]

       | FUN (a, x, bx) => O.MONO O.FUN $$ [([],[]) \ a, ([],[x]) \ bx]
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

       | PATH_TY ((u, a), m, n) => O.MONO O.PATH_TY $$ [([],[u]) \ a, ([],[]) \ m, ([],[]) \ n]
       | PATH_ABS (u, m) => O.MONO O.PATH_ABS $$ [([],[u]) \ m]
       | PATH_APP (m, r) => O.MONO O.PATH_APP $$ [([],[]) \ m, ([],[]) \ r]

       | EQUALITY (a, m, n) => O.MONO O.EQUALITY $$ [([],[]) \ a, ([],[]) \ m, ([],[]) \ n]

       | BOX args => intoBox args
       | CAP args => intoCap args

       | V (r, a, b, e) => O.MONO O.V $$ [([],[]) \ r, ([],[]) \ a, ([],[]) \ b, ([],[]) \ e]
       | VIN (r, m, n) => O.MONO O.VIN $$ [([],[]) \ r, ([],[]) \ m, ([],[]) \ n]
       | VPROJ (r, m, f) => O.MONO O.VPROJ $$ [([],[]) \ r, ([],[]) \ m, ([],[]) \ f]

       | UNIVERSE (l, k) => O.MONO O.UNIVERSE $$ [([],[]) \ L.into l, ([],[]) \ (O.MONO (O.KCONST k) $$ [])]

       | HCOM args => intoHcom args
       | COE {dir = (r1, r2), ty = (u, a), coercee} =>
           O.MONO O.COE $$ [([],[]) \ r1, ([],[]) \ r2, ([],[u]) \ a, ([],[]) \ coercee]
       | COM args => intoCom args

       | DIM0 => O.MONO O.DIM0' $$ []
       | DIM1 => O.MONO O.DIM1' $$ []
       | CUST => raise Fail "CUST"
       | META (x, tau) => check (x $# ([],[]), tau)

    val intoApp = into o APP
    val intoLam = into o LAM

    fun intoProd quantifiers last =
      let
        val lastVar = Var.named "_"
        val lastIndex = List.length quantifiers

        fun indexToLabel i = "proj" ^ Int.toString (i + 1)
        val projQuantifiers =
          ListUtil.mapWithIndex
            (fn (i, (var, tm)) => ((indexToLabel i, var), tm))
            quantifiers
        val projs = projQuantifiers @
          [((indexToLabel lastIndex, lastVar), last)]
      in
        into (RECORD projs)
      end

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)
       | O.MONO O.TV $ _ => TV
       | O.MONO O.AX $ _ => AX

       | O.MONO O.FCOM $ [_ \ r1, _ \ r2, _ \ cap, _ \ tubes] =>
           FCOM {dir = (r1, r2), cap = cap, tubes = outTubes tubes}

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
       | O.MONO O.LOOP $ [_ \ r] => LOOP r
       | O.MONO O.S1_REC $ [(_,[x]) \ cx, _ \ m, _ \ b, (_,[u]) \ l] => S1_REC ((x, cx), m, (b, (u, l)))

       | O.MONO O.FUN $ [_ \ a, (_,[x]) \ bx] => FUN (a, x, bx)
       | O.MONO O.LAM $ [(_,[x]) \ mx] => LAM (x, mx)
       | O.MONO O.APP $ [_ \ m, _ \ n] => APP (m, n)

       | O.MONO (O.RECORD lbls) $ tms => RECORD (outRecordFields (lbls, tms)) 
       | O.MONO (O.TUPLE lbls) $ tms => TUPLE (outTupleFields (lbls, tms))
       | O.MONO (O.PROJ lbl) $ [_ \ m] => PROJ (lbl, m)
       | O.MONO (O.TUPLE_UPDATE lbl) $ [_ \ n, _ \ m] => TUPLE_UPDATE ((lbl, n), m)

       | O.MONO O.PATH_TY $ [(_,[u]) \ a, _ \ m, _ \ n] => PATH_TY ((u, a), m, n)
       | O.MONO O.PATH_ABS $ [(_,[u]) \ m] => PATH_ABS (u, m)
       | O.MONO O.PATH_APP $ [_ \ m, _ \ r] => PATH_APP (m, r)

       | O.MONO O.EQUALITY $ [_ \ a, _ \ m, _ \ n] => EQUALITY (a, m, n)

       | O.MONO O.BOX $ [_ \ r1, _ \ r2, _ \ cap, _ \ boundaries] =>
           BOX {dir = (r1, r2), cap = cap, boundaries = outBoundaries boundaries}

       | O.MONO O.CAP $ [_ \ r1, _ \ r2, _ \ coercee, _ \ tubes] =>
           CAP {dir = (r1, r2), coercee = coercee, tubes = outTubes tubes}

       | O.MONO O.V $ [_ \ r, _ \ a, _ \ b, _ \ e] => V (r, a, b, e)
       | O.MONO O.VIN $ [_ \ r, _ \ m, _ \ n] => VIN (r, m, n)
       | O.MONO O.VPROJ $ [_ \ r, _ \ m, _ \ f] => VPROJ (r, m, f)

       | O.MONO O.UNIVERSE $ [_ \ l, _ \ k] =>
         let
           val O.MONO (O.KCONST k) $ _ = Tm.out k
         in
           UNIVERSE (L.out l, k)
         end

       | O.MONO O.HCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ tubes] =>
           HCOM {dir = (r1, r2), ty = ty, cap = cap, tubes = outTubes tubes}
       | O.MONO O.COE $ [_ \ r1, _ \ r2, (_,[u]) \ a, _ \ m] =>
           COE {dir = (r1, r2), ty = (u, a), coercee = m}

       | O.MONO O.DIM0' $ _ => DIM0
       | O.MONO O.DIM1' $ _ => DIM1

       | O.POLY (O.CUST _) $ _ => CUST
       | x $# ([],[]) => META (x, Tm.sort m)
       | _ => raise E.error [Fpp.text "Syntax view encountered unrecognized term", TermPrinter.ppTerm m]
  end
end
