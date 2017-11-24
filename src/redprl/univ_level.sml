structure RedPrlRawLevel =
struct
  structure E = RedPrlError
  structure D = Metavar.Ctx
  structure TP = TermPrinter

  (* normal form: minimum distance from zero and other variables *)
  type level' = IntInf.int * IntInf.int D.dict
  type level = level' option
  type t = level
  type term = RedPrlAbt.abt

  (* smart constructors *)
  fun const i = SOME (i, D.empty) : level
  val zero = const 0 : level
  fun plus (SOME (gap, gapmap) : level, i) =
    let
      fun shift x = x + i
    in
      SOME (shift gap, D.map shift gapmap)
    end
    | plus (NONE, 0) = NONE
    | plus (NONE, i) = E.raiseError
      (E.INVALID_LEVEL (Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "+", Fpp.text "omega", Fpp.text (IntInf.toString i)]))))
  fun max ls =
    let
      fun f (NONE, _) = NONE
        | f (_, NONE) = NONE
        | f (SOME (gap0, gapmap0), SOME (gap1, gapmap1)) =
          SOME (IntInf.max (gap0, gap1),
           D.union gapmap0 gapmap1 (fn (_, g0, g1) => IntInf.max (g0, g1)))
    in
      List.foldl f zero ls
    end
  val omega = NONE

  fun allBound f ((gap0, gapmap0), (gap1, gapmap1)) =
    f (gap0, gap1) andalso
    List.all
      (fn (var, g0) =>
        case D.find gapmap1 var of
          SOME g1 => f (g0, g1)
        | NONE => false)
      (D.toList gapmap0)
  val op <= : level * level -> bool =
    fn (_, NONE) => true
     | (NONE, _) => false
     | (SOME l1, SOME l2) => allBound IntInf.<= (l1, l2)
  val op < : level * level -> bool =
    fn (NONE, _) => false
     | (_, NONE) => true
     | (SOME l1, SOME l2) => allBound IntInf.< (l1, l2)
  fun eq' ((gap0, gapmap0) : level', (gap1, gapmap1) : level') =
    gap0 = gap1 andalso
      ListPair.allEq
        (fn ((v0, g0), (v1, g1)) => Var.eq (v0, v1) andalso g0 = g1)
        (D.toList gapmap0, D.toList gapmap1)
  val eq : level * level -> bool = OptionUtil.eq eq'

  (* augmented semi-lattice *)
  val top = omega
  fun residual (l0, l1) = if l1 <= l0 then NONE else SOME l0

  (* the code shared by the pretty printer and `into` *)
  fun into' intoOmega intoConst intoVarGap intoMax NONE = intoOmega
    | into' intoOmega intoConst intoVarGap intoMax (SOME (gap, gapmap) : level) =
    let
      val varGapList = List.map intoVarGap (D.toList gapmap)
      val gapImpliedByMap = D.foldl (fn (_, a, b) => IntInf.max (a, b)) 0 gapmap
      val args =
        if gap > gapImpliedByMap
        then intoConst gap :: varGapList
        else varGapList
    in
      intoMax args
    end

  (* pretty printer *)

  (* TODO
   *   `pretty.sml` should adopt the following algorithm so that `pretty`
   *   is the same as `ppParam o into`. *)
  val prettyOmega = Fpp.text "omega"
  val prettyConst = Fpp.text o IntInf.toString
  fun prettyVarGap (x, i) =
    if i = 0 then
      TermPrinter.ppVar x
    else if i = 1 then
      Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "++", TermPrinter.ppVar x]))
    else
      Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "+", TermPrinter.ppVar x, prettyConst i]))

  val prettyMax =
    fn [] => prettyConst 0
     | [arg] => arg
     | args => Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep (Fpp.text "lmax" :: args)))

  val pretty = into' prettyOmega prettyConst prettyVarGap prettyMax

  local
    open RedPrlAbt
    structure O = RedPrlOpData
    infix $ \ $$ $#
  in
    (* parser and generator *)
    fun out (tm : term) : level =
      case RedPrlAbt.out tm of
         x $# [] => SOME (0, D.singleton x 0)
       | O.LCONST i $ _ => const i
       | O.LPLUS i $ [_ \ l] => plus (out l, i)
       | O.LMAX $ [_ \ vec] => max (outVec vec)
       | O.LOMEGA $ _ => omega
       | _ => E.raiseError (E.INVALID_LEVEL (TermPrinter.ppTerm tm))

    and outVec tm = 
      let
        val O.MK_VEC _ $ xs = RedPrlAbt.out tm
      in
        List.map (fn _ \ x => out x) xs
      end
      handle Bind => 
        raise E.error [Fpp.text "Invalid level vector", TermPrinter.ppTerm tm]
        

    val omegaToTerm = O.LOMEGA $$ []

    fun constToTerm i = O.LCONST i $$ []

    fun makeVar x = 
      check (x $# [], O.LVL)

    fun makeVec xs = 
      O.MK_VEC (O.LVL, List.length xs) $$ List.map (fn x => [] \ x) xs

    fun varGapToTerm (x, i) =
      if i = 0 then makeVar x
      else O.LPLUS i $$ [[] \ makeVar x]

    val maxToTerm : abt list -> abt =
      fn [] => constToTerm 0
       | [arg] => arg
       | args => O.LMAX $$ [[] \ makeVec args]

    val into = into' omegaToTerm constToTerm varGapToTerm maxToTerm

    fun map f = out o f o into
  end
end

functor LevelUtil (L : REDPRL_LEVEL) =
struct
  open L
  structure WithKind =
  struct
    fun eq ((l1, k1), (l2, k2)) = L.eq (l1, l2) andalso k1 = k2
    fun residual ((l1, k1), (l2, k2)) =
      case (L.residual (l1, l2), RedPrlKind.residual (k1, k2)) of
         (NONE, NONE) => NONE
       | (SOME l, NONE) => SOME (l, RedPrlKind.top)
       | (NONE, SOME k) => SOME (top, k)
       | (SOME l, SOME k) => SOME (l, k)
  end
  structure WK = WithKind
end

structure RedPrlLevel = LevelUtil (RedPrlRawLevel)
