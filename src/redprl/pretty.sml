structure FppBasis = FppPrecedenceBasis (FppInitialBasis (FppPlainBasisTypes))
structure Fpp = FinalPrettyPrinter (FppBasis)

signature FINAL_PRINTER =
sig
  val execPP : Fpp.doc -> (int, unit) FppTypes.output
end

structure FinalPrinter :> FINAL_PRINTER =
struct
  open FppBasis Fpp

  local
    val initialEnv =
      {maxWidth = 80,
       maxRibbon = 60,
       layout = FppTypes.BREAK,
       failure = FppTypes.CANT_FAIL,
       nesting = 0,
       formatting = (),
       formatAnn = fn _ => ()}
  in
    fun execPP (m : unit m)  =
      #output (m emptyPrecEnv initialEnv {curLine = []})
  end
end

structure TermPrinter :
sig
  type t = RedPrlAbt.abt
  val toString : t -> string
  val ppTerm : t -> Fpp.doc
  val ppBinder : t RedPrlAbt.bview -> Fpp.doc
  val ppSort : RedPrlAbt.sort -> Fpp.doc
  val ppPsort : RedPrlAbt.psort -> Fpp.doc
  val ppValence : RedPrlAbt.valence -> Fpp.doc
  val ppVar : RedPrlAbt.variable -> Fpp.doc
  val ppSym : RedPrlAbt.symbol -> Fpp.doc
  val ppMeta : RedPrlAbt.metavariable -> Fpp.doc
  val ppParam : RedPrlAbt.param -> Fpp.doc
  val ppOperator : RedPrlAbt.operator -> Fpp.doc
  val ppKind : RedPrlKind.kind -> Fpp.doc
  val ppLabel : string -> Fpp.doc
end =
struct
  structure Abt = RedPrlAbt
  structure S = RedPrlSortData and P = struct open RedPrlParamData RedPrlParameterTerm end and Ar = Abt.O.Ar

  open FppBasis Fpp Abt
  structure O = RedPrlOpData

  type t = Abt.abt

  fun @@ (f, x) = f x
  infix 0 $ $$ $# \
  infixr 0 @@

  structure DebugPrintName = 
  struct
    val sym = Sym.DebugShow.toString
    val var = Var.DebugShow.toString
    val meta = Metavar.toString
  end

  structure NormalPrintName = 
  struct
    val sym = Sym.toString
    val var = Var.toString
    val meta = Metavar.toString
  end

  (* To debug scoping issues, switch below to DebugPrintName. *)
  structure PrintName = NormalPrintName

  val ppSym = text o PrintName.sym
  val ppVar = text o PrintName.var
  val ppKind = text o RedPrlKind.toString
  fun ppMeta x = seq [char #"#", text @@ PrintName.meta x]

  fun unlessEmpty xs m =
    case xs of
       [] => empty
     | _ => m

  val ppIntInf = text o IntInf.toString

  val rec ppParam =
    fn P.VAR x => ppSym x
     | P.APP P.DIM0 => text "0"
     | P.APP P.DIM1 => text "1"

  val ppParamWithSort =
    fn (p, NONE) => ppParam p
     | (p as P.VAR x, SOME _) => ppParam p
     | (p as P.APP P.DIM0, SOME S.DIM) => ppParam p (* sort DIM is the default for numerals *)
     | (p as P.APP P.DIM1, SOME S.DIM) => ppParam p (* sort DIM is the default for numerals *)
     | (p, SOME _) => raise Fail "ppParamWithSort encountered an invalid term."

  fun ppOperator theta =
    case theta of 
       O.POLY (O.CUST (opid, [], _)) => ppSym opid
     | O.POLY (O.CUST (opid, params, _)) => Atomic.braces @@ hsep @@ ppSym opid :: List.map ppParamWithSort params
     | _ =>  text @@ RedPrlOperator.toString PrintName.sym theta

  fun ppMetavarParams (x, ps) =
    case ps of
      [] => ppMeta x
    | ps => Atomic.braces @@ hsep @@ ppMeta x :: List.map (fn (p, _) => ppParam p) ps

  fun ppComHead name (r, r') =
    seq [text name, Atomic.braces @@ seq [ppParam r, text "~>", ppParam r']]

  fun ppComHeadBackward name (r, r') =
    seq [text name, Atomic.braces @@ seq [ppParam r, text "<~", ppParam r']]

  val ppLabel = text

  fun intersperse s xs =
    case xs of
       [] => []
     | [x] => [x]
     | x::xs => seq [x, s] :: intersperse s xs


  (* This is still quite rudimentary; we can learn to more interesting things like alignment, etc. *)

  fun multiFun (doms : (variable list option * abt) list) m =
    case Abt.out m of
       O.MONO O.FUN $ [_ \ a, (_, [x]) \ bx] =>
         if Abt.Var.Ctx.member (Abt.varctx bx) x then
           case doms of
              (SOME xs, a') :: doms' =>
                if Abt.eq (a, a') then
                  multiFun ((SOME (xs @ [x]), a) :: doms') bx
                else
                  multiFun ((SOME [x], a) :: doms) bx
            | _ => multiFun ((SOME [x], a) :: doms) bx
         else multiFun ((NONE, a) :: doms) bx
     | _ => (List.rev doms, m)

  fun multiLam (xs : variable list) m =
    case Abt.out m of
       O.MONO O.LAM $ [(_, [x]) \ mx] =>
         multiLam (x :: xs) mx
     | _ => (List.rev xs, m)

  fun multiApp m (ns : abt list) =
    case Abt.out m of
       O.MONO O.APP $ [_ \ m, _ \ n] =>
         multiApp m (n :: ns)
     | _ => (m, ns)

  fun multiPathAbs (us : symbol list) m =
    case Abt.out m of
       O.MONO O.PATH_ABS $ [([u], _) \ mu] =>
         multiPathAbs (u :: us) mu
     | _ => (List.rev us, m)

  fun multiPathApp m (rs : param list) =
    case Abt.out m of
       O.POLY (O.PATH_APP r) $ [_ \ m] =>
         multiPathApp m (r :: rs)
     | _ => (m, rs)

  fun printQuant opr (doms, cod) =
    Atomic.parens @@ expr @@ hvsep @@
      (text opr)
        :: List.map
            (fn (SOME xs, a) => Atomic.squares @@ hsep @@ List.map ppVar xs @ [char #":", ppTerm a]
              | (NONE, a) => ppTerm a)
            doms
          @ [ppTerm cod]

  and printLam (xs, m) =
    Atomic.parens @@ expr @@ hvsep @@
      [hvsep [text "lam", varBinding xs], align @@ ppTerm m]

  and printApp (m, ns) =
    Atomic.parens @@ expr @@ hvsep
      (char #"$" :: ppTerm m :: List.map ppTerm ns)

  and printPathAbs (us, m) =
    Atomic.parens @@ expr @@ hvsep @@
      [hvsep [text "abs", symBinding us], align @@ ppTerm m]

  and printPathApp (m, rs) =
    Atomic.parens @@ expr @@ hvsep
      (char #"@" :: ppTerm m :: List.map ppParam rs)

  and ppTerm m =
    case Abt.out m of
       O.POLY (O.HYP_REF (x, _)) $ [] => seq [char #",", ppVar x]
     | `x => ppVar x
     | O.POLY (O.FCOM (dir, eqs)) $ (cap :: tubes) =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [ppComHead "fcom" dir, ppBinder cap]
             :: [ppTubes (eqs, tubes)]
     | O.POLY (O.LOOP x) $ [] =>
         Atomic.parens @@ expr @@ hvsep @@ [text "loop", ppParam x]
     | O.MONO O.FUN $ _ =>
         printQuant "->" @@ multiFun [] m
     | O.MONO O.LAM $ _ =>
         printLam @@ multiLam [] m
     | O.MONO O.APP $ _ =>
         printApp @@ multiApp m []
     | O.MONO (O.RECORD []) $ _ => text "record"
     | O.MONO (O.RECORD lbls) $ args =>
         let
           val init = {fields = [], vars = []}
           val {fields, ...} = 
             ListPair.foldlEq
               (fn (lbl, (_, xs) \ ty, {fields, vars}) =>
                 let
                   val ren = ListPair.foldlEq (fn (x, var, ren) => Var.Ctx.insert ren x var) Var.Ctx.empty (xs, vars)
                   val ty' = RedPrlAbt.renameVars ren ty
                   val var = Var.named lbl
                 in
                   {fields = Atomic.squares (hsep [ppVar var, char #":", ppTerm ty']) :: fields,
                    vars = vars @ [var]}
                 end)
               init
               (lbls, args)
         in
           Atomic.parens @@ expr @@ hvsep @@ text "record" :: List.rev fields
         end 
     | O.MONO (O.TUPLE []) $ [] => text "tuple"
     | O.MONO (O.TUPLE lbls) $ data =>
         let
           fun pp (lbl, a) = Atomic.squares @@ hsep [ppLabel lbl, ppBinder a]
         in
           Atomic.parens @@ expr @@ hvsep
             [text "tuple", expr @@ hvsep @@ ListPair.mapEq pp (lbls, data)]
         end
     | O.MONO (O.PROJ lbl) $ [m] =>
         Atomic.parens @@ expr @@ hvsep [char #"!", ppLabel lbl, ppBinder m]
     | O.MONO O.PATH_ABS $ _ =>
         printPathAbs @@ multiPathAbs [] m
     | O.POLY (O.PATH_APP _) $ _ =>
         printPathApp @@ multiPathApp m []
     | O.MONO O.EQUALITY $ args =>
         Atomic.parens @@ expr @@ hvsep @@
           char #"=" :: List.map ppBinder args
     | O.POLY (O.BOX (dir, eqs)) $ (cap :: boundaries) =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [ppComHead "box" dir, ppBinder cap]
             :: [ppBoundaries (eqs, boundaries)]
     | O.POLY (O.CAP (dir, eqs)) $ (coercee :: tubes) =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [ppComHeadBackward "cap" dir, ppBinder coercee]
             :: [ppTubes (eqs, tubes)]
     | O.POLY (O.V r) $ args =>
         Atomic.parens @@ expr @@ hvsep @@ text "V" :: ppParam r :: List.map ppBinder args
     | O.POLY (O.VIN r) $ args =>
         Atomic.parens @@ expr @@ hvsep @@ text "Vin" :: ppParam r :: List.map ppBinder args
     | O.POLY (O.VPROJ r) $ args =>
         Atomic.parens @@ expr @@ hvsep @@ text "Vproj" :: ppParam r :: List.map ppBinder args
     | O.MONO (O.UNIVERSE k) $ [_ \ l] =>
         if k = RedPrlKind.top then
           Atomic.parens @@ expr @@ hvsep @@ [text "U", ppTerm l]
         else
           Atomic.parens @@ expr @@ hvsep @@ [text "U", ppTerm l, ppKind k]
     | O.POLY (O.HCOM (dir, eqs)) $ (ty :: cap :: tubes) =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [ppComHead "hcom" dir, ppBinder ty, ppBinder cap]
             :: [ppTubes (eqs, tubes)]

     | theta $ [] =>
        ppOperator theta
     | theta $ [([], []) \ arg] =>
        Atomic.parens @@ expr @@ hvsep @@ [ppOperator theta, atLevel 10 @@ ppTerm arg]
     | theta $ [(us, xs) \ arg] =>
        Atomic.parens @@ expr @@ hvsep [hvsep [ppOperator theta, seq [symBinding us, varBinding xs]], align @@ ppTerm arg]
     | theta $ args =>
        Atomic.parens @@ expr @@
          hvsep @@ ppOperator theta :: List.map ppBinder args

     | x $# (ps, []) => ppMetavarParams (x, ps)
     | x $# (ps, ms) =>
        Atomic.parens @@ expr @@ hvsep @@ ppMetavarParams (x, ps) :: List.map ppTerm ms

  and ppTubes (eqs, tubes) =
    expr @@ hvsep @@
      ListPair.mapEq
        (fn ((r1, r2), ([u], _) \ mu) =>
          Atomic.squares @@ hsep
            [seq [ppParam r1, Atomic.equals, ppParam r2],
             nest 1 @@ hvsep [Atomic.braces @@ ppSym u, ppTerm mu]])
        (eqs, tubes)

  and ppBoundaries (eqs, tubes) =
    expr @@ hvsep @@
      ListPair.mapEq
        (fn ((r1, r2), _ \ m) =>
          Atomic.squares @@ hsep
            [seq [ppParam r1, Atomic.equals, ppParam r2],
             nest 1 @@ ppTerm m])
        (eqs, tubes)


  and ppBinder ((us, xs) \ m) =
    case (us, xs) of
        ([], []) => atLevel 10 @@ ppTerm m
      | _ => grouped @@ hvsep [seq [symBinding us, varBinding xs], align @@ ppTerm m]

  and symBinding us =
    unlessEmpty us @@
      Atomic.braces @@
        hsep @@ List.map ppSym us

  and varBinding xs =
    unlessEmpty xs @@
      Atomic.squares @@
        hsep @@ List.map ppVar xs


  val ppSort = text o Ar.Vl.S.toString
  val ppPsort = text o Ar.Vl.PS.toString

  fun ppValence ((sigmas, taus), tau) =
    let
      val prefix =
        case (sigmas, taus) of
           ([], []) => empty
         | _ => seq [symSorts sigmas, varSorts taus, char #"."]
    in
      seq [prefix, ppSort tau]
    end

  and symSorts sigmas =
    unlessEmpty sigmas @@
      Atomic.braces @@
        hsep @@ intersperse Atomic.comma @@ List.map ppPsort sigmas

  and varSorts taus =
    unlessEmpty taus @@
      Atomic.squares @@
        hsep @@ intersperse Atomic.comma @@ List.map ppSort taus

  val toString =
    FppRenderPlainText.toString
      o FinalPrinter.execPP
      o ppTerm
end
