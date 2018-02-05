structure TermPrinter :
sig
  type t = RedPrlAbt.abt

  type env =
    {var : Fpp.doc Var.Ctx.dict,
     meta : Fpp.doc Var.Ctx.dict,
     level: int}

  val basicEnv : env
  val bindVars : RedPrlAbt.variable list -> env -> env

  val ppTerm' : env -> t -> Fpp.doc
  val ppBinder' : env -> t RedPrlAbt.bview -> Fpp.doc

  val ppVar' : env -> RedPrlAbt.variable -> Fpp.doc
  val ppMeta' : env -> RedPrlAbt.metavariable -> Fpp.doc

  val ppTerm : t -> Fpp.doc
  val ppBinder : t RedPrlAbt.bview -> Fpp.doc

  val toString : t -> string
  val ppSort : RedPrlAbt.sort -> Fpp.doc
  val ppValence : RedPrlAbt.valence -> Fpp.doc
  val ppArity : RedPrlArity.t -> Fpp.doc
  val ppVar : RedPrlAbt.variable -> Fpp.doc
  val ppMeta : RedPrlAbt.metavariable -> Fpp.doc
  val ppOperator : RedPrlAbt.operator -> Fpp.doc
  val ppKind : RedPrlKind.kind -> Fpp.doc
  val ppLabel : string -> Fpp.doc
end =
struct
  structure Abt = RedPrlAbt
  structure S = RedPrlSort and Ar = Abt.O.Ar

  open FppBasis Fpp Abt
  structure O = RedPrlOpData

  type t = Abt.abt

  fun @@ (f, x) = f x
  infix 0 $ $$ $# \
  infixr 0 @@

  structure DebugPrintName = 
  struct
    val var = Var.DebugShow.toString
    val meta = Metavar.DebugShow.toString
  end

  structure NormalPrintName = 
  struct
    val var = Var.toString
    val meta = Metavar.toString
  end

  (* To debug scoping issues, switch below to DebugPrintName. *)
  structure PrintName = NormalPrintName

  type env =
    {var : Fpp.doc Var.Ctx.dict,
     meta : Fpp.doc Var.Ctx.dict,
     level : int}

  val ppVar = text o PrintName.var
  val ppKind = text o RedPrlKind.toString
  fun ppMeta x = seq [char #"#", text @@ PrintName.meta x]

  fun bindVars xs ({var, meta, level} : env) : env = 
    let
      fun name x i = 
        case Sym.name x of 
           SOME s => text s
         | NONE => seq [char #"x", text (Int.toString i)]
      val (var', level') = List.foldl (fn (x, (rho, lvl)) => (Var.Ctx.insert rho x (name x lvl), lvl + 1)) (var, level) xs
    in
      {var = var',
       meta = meta,
       level = level'}
    end

  val basicEnv = 
    {var = Var.Ctx.empty,
     meta = Var.Ctx.empty,
     level = 0}

  fun unlessEmpty xs m =
    case xs of
       [] => empty
     | _ => m

  val ppIntInf = text o IntInf.toString

  fun ppOperator theta =
    case theta of
       O.CUST (opid, _) => text @@ MlId.toString opid
     | _ => text @@ RedPrlOperator.toString theta

  val ppLabel = text

  fun intersperse s =
    fn [] => []
     | [x] => [x]
     | x::xs => seq [x, s] :: intersperse s xs

  fun ppVar' (env : env) x = 
    Var.Ctx.lookup (#var env) x
    handle _ => Fpp.text "<free-var>"

  fun ppMeta' (env : env) x = 
    Metavar.Ctx.lookup (#meta env) x
    handle _ => Fpp.text "<free-meta>"


  (* This is still quite rudimentary; we can learn to more interesting things like alignment, etc. *)

  datatype ('a, 'b) binder = DIM of 'a | TERM of ('a * 'b)

  fun multiFunOrLine (doms : (variable list option, abt) binder list) m =
    case Abt.out m of
       O.FUN $ [_ \ a, [x] \ bx] =>
         if Abt.Var.Ctx.member (Abt.varctx bx) x then
           case doms of
              TERM (SOME xs, a') :: doms' =>
                if Abt.eq (a, a') then
                  multiFunOrLine (TERM (SOME (xs @ [x]), a) :: doms') bx
                else
                  multiFunOrLine (TERM (SOME [x], a) :: doms) bx
            | _ => multiFunOrLine (TERM (SOME [x], a) :: doms) bx
         else multiFunOrLine (TERM (NONE, a) :: doms) bx
     | O.LINE $ [[x] \ ax] =>
         if Abt.Var.Ctx.member (Abt.varctx ax) x then
           case doms of
              DIM (SOME xs) :: doms' =>
                multiFunOrLine (DIM (SOME (xs @ [x])) :: doms') ax
            | _ => multiFunOrLine (DIM (SOME [x]) :: doms) ax
         else multiFunOrLine (DIM NONE :: doms) ax
     | _ => (List.rev doms, m)

  fun multiLam (xs : variable list) m =
    case Abt.out m of
       O.LAM $ [[x] \ mx] =>
         multiLam (x :: xs) mx
     | _ => (List.rev xs, m)

  fun multiApp m (ns : abt list) =
    case Abt.out m of
       O.APP $ [_ \ m, _ \ n] =>
         multiApp m (n :: ns)
     | _ => (m, ns)

  fun multiAbs (us : variable list) m =
    case Abt.out m of
       O.ABS $ [[u] \ mu] =>
         multiAbs (u :: us) mu
     | _ => (List.rev us, m)

  fun multiDimApp m (rs : abt list) =
    case Abt.out m of
       O.DIM_APP $ [_ \ m, _ \ r] =>
         multiDimApp m (r :: rs)
     | _ => (m, rs)

  fun ppFunOrLinesInterior env (doms, cod) = 
    case doms of 
       [] => [ppTerm' env cod]
     | dom::doms =>
       (case dom of 
           TERM (SOME xs, a) =>
           let
             val env' = bindVars xs env
           in
             Atomic.squares (hsep (List.map (ppVar' env') xs @ [char #":", ppTerm' env a]))
               :: ppFunOrLinesInterior env' (doms, cod)
           end
         | TERM (NONE, a) => ppTerm' env a :: ppFunOrLinesInterior env (doms, cod)
         | DIM (SOME xs) =>
           let
             val env' = bindVars xs env
           in
             Atomic.squares (hsep (List.map (ppVar' env') xs @ [char #":", text "dim"]))
               :: ppFunOrLinesInterior env' (doms, cod)
           end
         | DIM NONE => text "dim" :: ppFunOrLinesInterior env (doms, cod))

  and printFunOrLine env (doms, cod) =
    Atomic.parens @@ expr @@ hvsep @@
      text "->" :: ppFunOrLinesInterior env (doms, cod)

  and printLam env (xs, m) =
    Atomic.parens @@ expr @@ hvsep @@
      [hvsep [text "lam", varBinding env xs], align @@ ppTerm' (bindVars xs env) m]

  and printApp env (m, ns) =
    Atomic.parens @@ expr @@ hvsep
      (char #"$" :: ppTerm' env m :: List.map (ppTerm' env) ns)

  and printAbs env (us, m) =
    Atomic.parens @@ expr @@ hvsep @@
      [hvsep [text "abs", varBinding env us], align @@ ppTerm' (bindVars us env) m]

  and printDimApp env (m, rs) =
    Atomic.parens @@ expr @@ hvsep
      (char #"@" :: ppTerm' env m :: List.map (ppTerm' env) rs)

  and ppDir env (r, r') = seq [ppTerm' env r, text "~>", ppTerm' env r']

  and ppBackwardDir env (r, r') = seq [ppTerm' env r, text "<~", ppTerm' env r']

  and ppTerm' env m =
    case Abt.out m of
       `x => ppVar' env x
     | O.FCOM $ [_ \ r1, _ \ r2, _ \ cap, _ \ system] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "fcom", ppDir env (r1, r2), ppTerm' env cap]
             :: [ppVector env system]

     | O.HCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ system] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "hcom", ppDir env (r1, r2), ppTerm' env ty, ppTerm' env cap]
             :: [ppVector env system]
     | O.GHCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ system] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "ghcom", ppDir env (r1, r2), ppTerm' env ty, ppTerm' env cap]
             :: [ppVector env system]
     | O.COE $ [_ \ r1, _ \ r2, ty, _ \ coercee] =>
         Atomic.parens @@ expr @@ hvsep @@
           [text "coe", ppDir env (r1, r2), ppBinder' env ty, ppTerm' env coercee]
     | O.COM $ [_ \ r1, _ \ r2, ty, _ \ cap, _ \ system] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "com", ppDir env (r1, r2), ppBinder' env ty, ppTerm' env cap]
             :: [ppVector env system]
     | O.GCOM $ [_ \ r1, _ \ r2, ty, _ \ cap, _ \ system] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "gcom", ppDir env (r1, r2), ppBinder' env ty, ppTerm' env cap]
             :: [ppVector env system]

     | O.LOOP $ [_ \ r] =>
         Atomic.parens @@ expr @@ hvsep @@ [text "loop", ppTerm' env r]
     | O.FUN $ _ =>
         printFunOrLine env @@ multiFunOrLine [] m
     | O.LAM $ _ =>
         printLam env @@ multiLam [] m
     | O.APP $ _ =>
         printApp env @@ multiApp m []
     | O.RECORD [] $ _ => text "record"
     | O.RECORD lbls $ args =>
         let
           val init = {fields = [], vars = [], env = env}
           val {fields, ...} = 
             ListPair.foldlEq
               (fn (lbl, xs \ ty, {fields, vars, env}) =>
                 let
                   val ren = ListPair.foldlEq (fn (x, var, ren) => Var.Ctx.insert ren x var) Var.Ctx.empty (xs, vars)
                   val ty' = RedPrlAbt.renameVars ren ty
                   val var = Var.named lbl
                   val env' = bindVars [var] env
                 in
                   {fields = Atomic.squares (hsep [ppVar' env' var, char #":", ppTerm' env ty']) :: fields,
                    vars = vars @ [var],
                    env = env'}
                 end)
               init
               (lbls, args)
         in
           Atomic.parens @@ expr @@ hvsep @@ text "record" :: List.rev fields
         end 
     | O.TUPLE [] $ [] => text "tuple"
     | O.TUPLE lbls $ data =>
         let
           fun pp (lbl, a) = Atomic.squares @@ hsep [ppLabel lbl, ppBinder' env a]
         in
           Atomic.parens @@ expr @@ hvsep
             [text "tuple", expr @@ hvsep @@ ListPair.mapEq pp (lbls, data)]
         end
     | O.PROJ lbl $ [m] =>
         Atomic.parens @@ expr @@ hvsep [char #"!", ppLabel lbl, ppBinder' env m]
     | O.LINE $ _ =>
         printFunOrLine env @@ multiFunOrLine [] m
     | O.ABS $ _ =>
         printAbs env @@ multiAbs [] m
     | O.DIM_APP $ _ =>
         printDimApp env @@ multiDimApp m []
     | O.EQUALITY $ [_ \ ty, _ \ m, _ \ n] =>
         Atomic.parens @@ expr @@ hvsep
           (if Abt.eq (m, n)
            then [text "mem", ppTerm' env ty, ppTerm' env m]
            else [char #"=", ppTerm' env ty, ppTerm' env m, ppTerm' env n])
     | O.BOX $ [_ \ r1, _ \ r2, cap, _ \ boundaries] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "box", ppDir env (r1, r2), ppBinder' env cap]
             :: [ppVector env boundaries]
     | O.CAP $ [_ \ r1, _ \ r2, coercee, _ \ tubes] =>
         Atomic.parens @@ expr @@ hvsep @@
           hvsep [text "cap", ppBackwardDir env (r1, r2), ppBinder' env coercee]
             :: [ppVector env tubes]
     | O.V $ args =>
         Atomic.parens @@ expr @@ hvsep @@ text "V" :: List.map (ppBinder' env) args
     | O.VIN $ args =>
         Atomic.parens @@ expr @@ hvsep @@ text "Vin" :: List.map (ppBinder' env) args
     | O.VPROJ $ args =>
         Atomic.parens @@ expr @@ hvsep @@ text "Vproj" :: List.map (ppBinder' env) args
     | O.UNIVERSE $ [_ \ l, _ \ k] =>
         Atomic.parens @@ expr @@ hvsep @@ [text "U", ppTerm' env l, ppTerm' env k]

     | O.DIM0 $ _ => char #"0"
     | O.DIM1 $ _ => char #"1"
     | O.MK_TUBE $ [_ \ r1, _ \ r2, tube]  =>
       Atomic.squares @@ hsep
         [seq [ppTerm' env r1, Atomic.equals, ppTerm' env r2],
          nest 1 @@ ppBinder' env tube]
     | O.MK_BDRY $ [_ \ r1, _ \ r2, _ \ m] =>
       Atomic.squares @@ hsep
         [seq [ppTerm' env r1, Atomic.equals, ppTerm' env r2],
          nest 1 @@ ppTerm' env m]
     | O.MK_ANY _ $ [_ \ m] => ppTerm' env m

     | O.LCONST i $ _ => ppIntInf i
     | O.LPLUS 0 $ [_ \ l] => ppTerm' env l
     | O.LPLUS 1 $ [_ \ l] => Atomic.parens @@ expr @@ hvsep @@ [text "++", ppTerm' env l]
     | O.LPLUS i $ [_ \ l] => Atomic.parens @@ expr @@ hvsep @@ [text "+", ppTerm' env l, ppIntInf i]
     | O.LMAX $ [_ \ vec] =>
         (case RedPrlAbt.out vec of
             O.MK_VEC _ $ [] => ppIntInf 0
           | O.MK_VEC _ $ [_ \ l] => ppTerm' env l
           | O.MK_VEC _ $ ls =>
               Atomic.parens @@ expr @@ hvsep @@
                 (text "lmax" :: ListUtil.revMap (fn _ \ l => ppTerm' env l) ls)
           | _ => raise Fail "invalid vector")

     | theta $ [] =>
        ppOperator theta
     | theta $ [[] \ arg] =>
        Atomic.parens @@ expr @@ hvsep @@ [ppOperator theta, atLevel 10 @@ ppTerm' env arg]
     | theta $ [xs \ arg] =>
        Atomic.parens @@ expr @@ hvsep [hvsep [ppOperator theta, varBinding env xs], align @@ ppTerm' (bindVars xs env) arg]
     | theta $ args =>
        Atomic.parens @@ expr @@
          hvsep @@ ppOperator theta :: List.map (ppBinder' env) args

     | x $# [] => ppMeta x
     | x $# ms => Atomic.parens @@ expr @@ hvsep @@ ppMeta x :: List.map (ppTerm' env) ms

  and ppVector env (vec : abt) : Fpp.doc =
    case Abt.out vec of
       O.MK_VEC _ $ args => 
         expr @@ hvsep @@ 
           List.map (fn _ \ t => ppTerm' env t) args
     | _ => raise Fail "invalid vector"

  and ppBinder' env (xs \ m) =
    case xs of
        [] => atLevel 10 @@ ppTerm' env m
      | _ => grouped @@ hvsep [varBinding env xs, align @@ ppTerm' (bindVars xs env) m]

  and varBinding env xs =
    unlessEmpty xs @@
      Atomic.squares @@
        hsep @@ List.map (ppVar' (bindVars xs env)) xs


  val ppSort = text o Ar.Vl.S.toString

  val ppTerm = ppTerm' basicEnv
  val ppBinder = ppBinder' basicEnv

  fun ppValence (taus, tau) =
    let
      val prefix =
        case taus of
           [] => empty
         | _ => seq [varSorts taus, char #"."]
    in
      seq [prefix, ppSort tau]
    end

  and ppArity (vls, tau) =
    let
      val vls' = 
        Fpp.collection
          (Fpp.char #"[")
          (Fpp.char #"]")
          Fpp.Atomic.comma
          (List.map ppValence vls)
    in
      Fpp.hsep [vls', Fpp.text "=>", ppSort tau]
    end

  and varSorts taus =
    unlessEmpty taus @@
      Atomic.squares @@
        hsep @@ intersperse Atomic.comma @@ List.map ppSort taus

  val toString =
    FppRenderPlainText.toString
      o FinalPrinter.execPP
      o ppTerm
end
