structure SyntaxView =
struct
  structure Tm = RedPrlAbt
  structure K = RedPrlKind
  structure L = RedPrlLevel
  type variable = Tm.variable
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
   | S1 | BASE | LOOP of 'a | S1_REC of (variable * 'a) * 'a * ('a * (variable * 'a))
   (* function: lambda and app *)
   | FUN of 'a * variable * 'a | LAM of variable * 'a | APP of 'a * 'a
   (* record *)
   | RECORD of ((string * variable) * 'a) list
   | TUPLE of (label * 'a) list | PROJ of string * 'a | TUPLE_UPDATE of (string * 'a) * 'a
   (* path: path abstraction and path application *)
   | PATH of (variable * 'a) * 'a * 'a | ABS of variable * 'a | DIM_APP of 'a * 'a
   | LINE of variable * 'a
   (* pushouts *)
   | PUSHOUT of 'a * 'a * 'a * (variable * 'a) * (variable * 'a)
   | LEFT of 'a | RIGHT of 'a
   | GLUE of 'a * 'a * 'a * 'a
   | PUSHOUT_REC of (variable * 'a) * 'a * ((variable * 'a) * (variable * 'a) * (variable * variable * 'a))
   (* coequalizers *)
   | COEQUALIZER of 'a * 'a * (variable * 'a) * (variable * 'a)
   | CECOD of 'a
   | CEDOM of 'a * 'a * 'a * 'a
   | COEQUALIZER_REC of (variable * 'a) * 'a * ((variable * 'a) * (variable * variable * 'a))
   (* equality *)
   | EQUALITY of 'a * 'a * 'a
   (* fcom types *)
   | BOX of {dir: dir, cap: 'a, boundaries: (equation * 'a) list}
   | CAP of {dir: dir, tubes: (equation * (variable * 'a)) list, coercee: 'a}
   (* V *)
   | V of 'a * 'a * 'a * 'a
   | VIN of 'a * 'a * 'a | VPROJ of 'a * 'a * 'a
   (* universes *)
   | UNIVERSE of L.level * kind
   (* hcom operator *)
   | HCOM of {dir: dir, ty: 'a, cap: 'a, tubes: (equation * (variable * 'a)) list}
   (* ghcom operator *)
   | GHCOM of {dir: dir, ty: 'a, cap: 'a, tubes: (equation * (variable * 'a)) list}
   (* coe operator *)
   | COE of {dir: dir, ty: (variable * 'a), coercee: 'a}
   (* com operator *)
   | COM of {dir: dir, ty: (variable * 'a), cap: 'a, tubes: (equation * (variable * 'a)) list}
   (* gcom operator *)
   | GCOM of {dir: dir, ty: (variable * 'a), cap: 'a, tubes: (equation * (variable * 'a)) list}

   | DIM0 | DIM1

   (* custom operators *)
   | CUST
   (* meta *)
   | META of Tm.metavariable * sort



  local
    open Tm
    structure O = RedPrlOperator and E = RedPrlError
    infix $ $$ $# \
  in
    fun outVec' (f : abt -> 'a) (vec : abt) : 'a list =
      let
        val O.MK_VEC _ $ args = Tm.out vec
      in
        List.map (fn _ \ t => f t) args
      end

    val outVec = outVec' (fn x => x)

    fun unpackAny m =
      let
        val O.MK_ANY _ $ [_ \ m'] = Tm.out m
      in
        m'
      end

    fun outSelector (s : abt) : Tm.variable Selector.t =
      case Tm.out s of 
         O.SEL_CONCL $ _ => Selector.IN_CONCL
       | O.SEL_HYP $ [_ \ e] =>
         (case Tm.out (unpackAny e) of
             `x => Selector.IN_HYP x
           | _ => raise Fail "Invalid selector")

    fun outAccessor (s : abt) : Accessor.t  =
      case Tm.out s of
         O.ACC_WHOLE $ _ => Accessor.WHOLE
       | O.ACC_TYPE $ _ => Accessor.PART_TYPE
       | O.ACC_LEFT $ _ => Accessor.PART_LEFT
       | O.ACC_RIGHT $ _ => Accessor.PART_RIGHT

    fun outTube tube = 
      let
        val O.MK_TUBE $ [_ \ r1, _ \ r2, [u] \ mu] = Tm.out tube
      in
        ((r1, r2), (u, mu))
      end

    fun outBoundary boundary = 
      let
        val O.MK_BDRY $ [_ \ r1, _ \ r2, _ \ m] = Tm.out boundary
      in
        ((r1, r2), m)
      end

    (* TODO: use outVec' *)
    fun outTubes system =
      let
        val O.MK_VEC _ $ args = Tm.out system
      in
        List.map (fn _ \ t => outTube t) args
      end

    fun outBoundaries boundaries =
      let
        val O.MK_VEC _ $ args = Tm.out boundaries
      in
        List.map (fn _ \ b => outBoundary b) args
      end

    fun intoTube ((r1, r2), (u, e)) = 
      O.MK_TUBE $$ 
        [[] \ r1,
         [] \ r2,
         [u] \ e]

    fun intoBoundary ((r1, r2), e) = 
      O.MK_BDRY $$
        [[] \ r1,
         [] \ r2,
         [] \ e]


    fun intoTubes tubes = 
      let
        val n = List.length tubes
      in
        O.MK_VEC (O.TUBE, n) $$
          List.map (fn t => [] \ intoTube t) tubes
      end

    fun intoBoundaries boundaries = 
      let
        val n = List.length boundaries
      in
        O.MK_VEC (O.BDRY, n) $$
          List.map (fn b => [] \ intoBoundary b) boundaries
      end
  end

  local
    open Tm
    structure O = RedPrlOperator and E = RedPrlError
    infix $ $$ $# \


    fun intoFcom {dir = (r1, r2), cap, tubes} =
      O.FCOM $$
        [[] \ r1,
         [] \ r2,
         [] \ cap,
         [] \ intoTubes tubes]

    fun intoHcom {dir = (r1, r2), ty, cap, tubes} =
      O.HCOM $$ 
        [[] \ r1,
         [] \ r2,
         [] \ ty,
         [] \ cap,
         [] \ intoTubes tubes]

    fun intoGhcom {dir = (r1, r2), ty, cap, tubes} =
      O.GHCOM $$
        [[] \ r1,
         [] \ r2,
         [] \ ty,
         [] \ cap,
         [] \ intoTubes tubes]

    fun intoCom {dir = (r1, r2), ty=(u,a), cap, tubes} =
      O.COM $$ 
        [[] \ r1,
         [] \ r2,
         [u] \ a,
         [] \ cap,
         [] \ intoTubes tubes]

    fun intoGcom {dir = (r1, r2), ty=(u,a), cap, tubes} =
      O.GCOM $$
        [[] \ r1,
         [] \ r2,
         [u] \ a,
         [] \ cap,
         [] \ intoTubes tubes]


    (* fun outBoudaries (eqs, boundaries) =
      ListPair.zipEq (eqs, List.map (fn (_ \ b) => b) boundaries) *)

    fun intoBox {dir = (r1, r2), cap, boundaries} =
      O.BOX $$ 
        [[] \ r1,
         [] \ r2,
         [] \ cap,
         [] \ intoBoundaries boundaries]

    fun intoCap {dir = (r1, r2), coercee, tubes} =
      O.CAP $$ 
        [[] \ r1,
         [] \ r2,
         [] \ coercee,
         [] \ intoTubes tubes]

    fun outRecordFields (lbls, args) =
      let
        val init = {rcd = [], vars = []}
        val {rcd, ...} = 
          ListPair.foldlEq
            (fn (lbl, xs \ ty, {rcd, vars}) =>
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
        val tms = List.map (fn tm => [] \ tm) tms
      in
        (lbls, tms)
      end

    fun outTupleFields (lbls, args) =
      ListPair.mapEq (fn (lbl, (_ \ tm)) => (lbl, tm)) (lbls, args)

    val into =
      fn VAR (x, tau) => check (`x, tau)

       | AX => O.AX $$ []

       | FCOM args => intoFcom args

       | BOOL => O.BOOL $$ []
       | TT => O.TT $$ []
       | FF => O.FF $$ []
       | IF (m, (t, f)) => O.IF $$ [[] \ m, [] \ t, [] \ f]

       | WBOOL => O.WBOOL $$ []
       | WIF ((x, cx), m, (t, f)) => O.WIF $$ [[x] \ cx, [] \ m, [] \ t, [] \ f]

       | NAT => O.NAT $$ []
       | ZERO => O.ZERO $$ []
       | SUCC m => O.SUCC $$ [[] \ m]
       | NAT_REC (m, (n, (a, b, p))) => O.NAT_REC $$ [[] \ m, [] \ n, [a,b] \ p]

       | INT => O.INT $$ []
       | NEGSUCC m => O.NEGSUCC $$ [[] \ m]
       | INT_REC (m, (n, (a, b, p), q, (c, d, r))) =>
           O.INT_REC $$ [[] \ m, [] \ n, [a,b] \ p, [] \ q, [c,d] \ r]

       | VOID => O.VOID $$ []

       | S1 => O.S1 $$ []
       | BASE => O.BASE $$ []
       | LOOP r => O.LOOP $$ [[] \ r]
       | S1_REC ((x, cx), m, (b, (u, l))) => O.S1_REC $$ [[x] \ cx, [] \ m, [] \ b, [u] \ l]

       | FUN (a, x, bx) => O.FUN $$ [[] \ a, [x] \ bx]
       | LAM (x, mx) => O.LAM $$ [[x] \ mx]
       | APP (m, n) => O.APP $$ [[] \ m, [] \ n]

       | RECORD fields =>
            let
             val init = {labels = [], args = [], vars = []}
             val {labels, args, ...} =
               List.foldl
                 (fn (((lbl, var), ty), {labels, args, vars}) =>
                     {labels = lbl :: labels,
                      vars = vars @ [var],
                      args = (vars \ ty) :: args})
                 init
                 fields
           in
             O.RECORD (List.rev labels) $$ List.rev args
           end
       | TUPLE fs =>
           let
             val (lbls, tys) = intoTupleFields fs
           in
             O.TUPLE lbls $$ tys
           end
       | PROJ (lbl, a) => O.PROJ lbl $$ [[] \ a]
       | TUPLE_UPDATE ((lbl, n), m) => O.TUPLE_UPDATE lbl $$ [[] \ n, [] \ m]

       | PATH ((u, a), m, n) => O.PATH $$ [[u] \ a, [] \ m, [] \ n]
       | LINE (u, a) => O.LINE $$ [[u] \ a]
       | ABS (u, m) => O.ABS $$ [[u] \ m]
       | DIM_APP (m, r) => O.DIM_APP $$ [[] \ m, [] \ r]

       | PUSHOUT (a, b, c, (x, fx), (y, gy)) =>
           O.PUSHOUT $$ [[] \ a, [] \ b, [] \ c, [x] \ fx, [y] \ gy]
       | LEFT m => O.LEFT $$ [[] \ m]
       | RIGHT m => O.RIGHT $$ [[] \ m]
       | GLUE (r, m, fm, gm) => O.GLUE $$ [[] \ r, [] \ m, [] \ fm, [] \ gm]
       | PUSHOUT_REC ((x, cx), m, ((y, ly), (z, rz), (w1, w2, gw))) =>
           O.PUSHOUT_REC $$ [[x] \ cx, [] \ m, [y] \ ly, [z] \ rz, [w1, w2] \ gw]

       | COEQUALIZER (a, b, (x, fx), (y, gy)) =>
           O.COEQUALIZER $$ [[] \ a, [] \ b, [x] \ fx, [y] \ gy]
       | CECOD m => O.CECOD $$ [[] \ m]
       | CEDOM (r, m, fm, gm) => O.CEDOM $$ [[] \ r, [] \ m, [] \ fm, [] \ gm]
       | COEQUALIZER_REC ((x, px), m, ((y, cy), (w1, w2, dw))) =>
           O.COEQUALIZER_REC $$ [[x] \ px, [] \ m, [y] \ cy, [w1, w2] \ dw]

       | EQUALITY (a, m, n) => O.EQUALITY $$ [[] \ a, [] \ m, [] \ n]

       | BOX args => intoBox args
       | CAP args => intoCap args

       | V (r, a, b, e) => O.V $$ [[] \ r, [] \ a, [] \ b, [] \ e]
       | VIN (r, m, n) => O.VIN $$ [[] \ r, [] \ m, [] \ n]
       | VPROJ (r, m, f) => O.VPROJ $$ [[] \ r, [] \ m, [] \ f]

       | UNIVERSE (l, k) => O.UNIVERSE $$ [[] \ L.into l, [] \ (O.KCONST k $$ [])]

       | HCOM args => intoHcom args
       | GHCOM args => intoGhcom args
       | COE {dir = (r1, r2), ty = (u, a), coercee} =>
           O.COE $$ [[] \ r1, [] \ r2, [u] \ a, [] \ coercee]
       | COM args => intoCom args
       | GCOM args => intoGcom args

       | DIM0 => O.DIM0 $$ []
       | DIM1 => O.DIM1 $$ []
       | CUST => raise Fail "CUST"
       | META (x, tau) => check (x $# [], tau)

    val intoApp = into o APP
    val intoLam = into o LAM
    fun intoDim 0 = into DIM0
      | intoDim 1 = into DIM1
      | intoDim i = E.raiseError (E.INVALID_DIMENSION (Fpp.text (IntInf.toString i)))

    val intoFcom = into o FCOM
    val intoHcom = into o HCOM
    val intoGhcom = into o GHCOM
    val intoCoe = into o COE
    val intoCom = into o COM
    val intoGcom = into o GCOM

    fun intoFst m = into (PROJ (O.indexToLabel 0, m))
    fun intoSnd m = into (PROJ (O.indexToLabel 1, m))
    val intoAnonTuple = into o TUPLE o
      ListUtil.mapWithIndex (fn (i, tm) => (O.indexToLabel i, tm))

    fun intoProd quantifiers last =
      let
        val lastVar = Var.named "_"
        val lastIndex = List.length quantifiers

        val projQuantifiers =
          ListUtil.mapWithIndex
            (fn (i, (var, tm)) => ((O.indexToLabel i, var), tm))
            quantifiers
        val projs = projQuantifiers @
          [((O.indexToLabel lastIndex, lastVar), last)]
      in
        into (RECORD projs)
      end

    val intoEq = into o EQUALITY
    val intoU = into o UNIVERSE

    fun out m =
      case Tm.out m of
         `x => VAR (x, Tm.sort m)
       | O.AX $ _ => AX

       | O.FCOM $ [_ \ r1, _ \ r2, _ \ cap, _ \ tubes] =>
           FCOM {dir = (r1, r2), cap = cap, tubes = outTubes tubes}

       | O.BOOL $ _ => BOOL
       | O.TT $ _ => TT
       | O.FF $ _ => FF
       | O.IF $ [_ \ m, _ \ t, _ \ f] => IF (m, (t, f))

       | O.WBOOL $ _ => WBOOL
       | O.WIF $ [[x] \ cx, _ \ m, _ \ t, _ \ f] => WIF ((x, cx), m, (t, f))

       | O.NAT $ _ => NAT
       | O.ZERO $ _ => ZERO
       | O.SUCC $ [_ \ m] => SUCC m
       | O.NAT_REC $ [_ \ m, _ \ n, [a,b] \ p] => NAT_REC (m, (n, (a, b, p)))

       | O.INT $ _ => INT
       | O.NEGSUCC $ [_ \ m] => NEGSUCC m
       | O.INT_REC $ [_ \ m, _ \ n, [a,b] \ p, _ \ q, [c,d] \ r] =>
           INT_REC (m, (n, (a, b, p), q, (c, d, r)))

       | O.VOID $ _ => VOID

       | O.S1 $ _ => S1
       | O.BASE $ _ => BASE
       | O.LOOP $ [_ \ r] => LOOP r
       | O.S1_REC $ [[x] \ cx, _ \ m, _ \ b, [u] \ l] => S1_REC ((x, cx), m, (b, (u, l)))

       | O.FUN $ [_ \ a, [x] \ bx] => FUN (a, x, bx)
       | O.LAM $ [[x] \ mx] => LAM (x, mx)
       | O.APP $ [_ \ m, _ \ n] => APP (m, n)

       | O.RECORD lbls $ tms => RECORD (outRecordFields (lbls, tms)) 
       | O.TUPLE lbls $ tms => TUPLE (outTupleFields (lbls, tms))
       | O.PROJ lbl $ [_ \ m] => PROJ (lbl, m)
       | O.TUPLE_UPDATE lbl $ [_ \ n, _ \ m] => TUPLE_UPDATE ((lbl, n), m)

       | O.PATH $ [[u] \ a, _ \ m, _ \ n] => PATH ((u, a), m, n)
       | O.LINE $ [[u] \ a] => LINE (u, a)
       | O.ABS $ [[u] \ m] => ABS (u, m)
       | O.DIM_APP $ [_ \ m, _ \ r] => DIM_APP (m, r)

       | O.PUSHOUT $ [_ \ a, _ \ b, _ \ c, [x] \ fx, [y] \ gy] =>
           PUSHOUT (a, b, c, (x, fx), (y, gy))
       | O.LEFT $ [_ \ m] => LEFT m
       | O.RIGHT $ [_ \ m] => RIGHT m
       | O.GLUE $ [_ \ r, _ \ m, _ \ fm, _ \ gm] => GLUE (r, m, fm, gm)
       | O.PUSHOUT_REC $ [[x] \ cx, _ \ m, [y] \ ly, [z] \ rz, [w1, w2] \ gw] =>
           PUSHOUT_REC ((x, cx), m, ((y, ly), (z, rz), (w1, w2, gw)))

       | O.COEQUALIZER $ [_ \ a, _ \ b, [x] \ fx, [y] \ gy] =>
           COEQUALIZER (a, b, (x, fx), (y, gy))
       | O.CECOD $ [_ \ m] => CECOD m
       | O.CEDOM $ [_ \ r, _ \ m, _ \ fm, _ \ gm] => CEDOM (r, m, fm, gm)
       | O.COEQUALIZER_REC $ [[x] \ px, _ \ m, [y] \ cy,  [w1, w2] \ dw] =>
           COEQUALIZER_REC ((x, px), m, ((y, cy), (w1, w2, dw)))

       | O.EQUALITY $ [_ \ a, _ \ m, _ \ n] => EQUALITY (a, m, n)

       | O.BOX $ [_ \ r1, _ \ r2, _ \ cap, _ \ boundaries] =>
           BOX {dir = (r1, r2), cap = cap, boundaries = outBoundaries boundaries}
       | O.CAP $ [_ \ r1, _ \ r2, _ \ coercee, _ \ tubes] =>
           CAP {dir = (r1, r2), coercee = coercee, tubes = outTubes tubes}

       | O.V $ [_ \ r, _ \ a, _ \ b, _ \ e] => V (r, a, b, e)
       | O.VIN $ [_ \ r, _ \ m, _ \ n] => VIN (r, m, n)
       | O.VPROJ $ [_ \ r, _ \ m, _ \ f] => VPROJ (r, m, f)

       | O.UNIVERSE $ [_ \ l, _ \ k] =>
         let
           val O.KCONST k $ _ = Tm.out k
         in
           UNIVERSE (L.out l, k)
         end

       | O.HCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ tubes] =>
           HCOM {dir = (r1, r2), ty = ty, cap = cap, tubes = outTubes tubes}
       | O.GHCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ tubes] =>
           GHCOM {dir = (r1, r2), ty = ty, cap = cap, tubes = outTubes tubes}
       | O.COE $ [_ \ r1, _ \ r2, [u] \ a, _ \ m] =>
           COE {dir = (r1, r2), ty = (u, a), coercee = m}
       | O.COM $ [_ \ r1, _ \ r2, [u] \ ty, _ \ cap, _ \ tubes] =>
           COM {dir = (r1, r2), ty = (u, ty), cap = cap, tubes = outTubes tubes}
       | O.GCOM $ [_ \ r1, _ \ r2, [u] \ ty, _ \ cap, _ \ tubes] =>
           GCOM {dir = (r1, r2), ty = (u, ty), cap = cap, tubes = outTubes tubes}

       | O.DIM0 $ _ => DIM0
       | O.DIM1 $ _ => DIM1

       | O.CUST _ $ _ => CUST
       | x $# [] => META (x, Tm.sort m)
       | _ => raise E.error [Fpp.text "Syntax view encountered unrecognized term", TermPrinter.ppTerm m]
  end
end
