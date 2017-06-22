structure FppBasis = FppPrecedenceBasis (FppInitialBasis (FppPlainBasisTypes))
structure Fpp = FinalPrettyPrinter (FppBasis)

signature FINAL_PRINTER = 
sig
  type doc = unit Fpp.m
  val execPP : doc -> (int, unit) FppTypes.output
end

structure FinalPrinter :> FINAL_PRINTER = 
struct
  open FppBasis Fpp
  type doc = unit m

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
  val ppTerm : t -> FinalPrinter.doc
  val ppSort : RedPrlAbt.sort -> FinalPrinter.doc
  val ppPsort : RedPrlAbt.psort -> FinalPrinter.doc
  val ppValence : RedPrlAbt.valence -> FinalPrinter.doc
end =
struct
  structure Abt = RedPrlAbt
  structure P = RedPrlParameterTerm and Ar = Abt.O.Ar

  open FppBasis Fpp Abt
  structure O = RedPrlOpData

  type t = Abt.abt

  fun @@ (f, x) = f x
  infix 0 $ $$ $# \
  infixr 0 @@

  val ppVar = text o Var.toString
  val ppParam = text o P.toString Sym.toString

  fun unlessEmpty xs m = 
    case xs of 
       [] => empty
     | _ => m

  val ppOperator = 
    text o RedPrlOperator.toString Sym.toString

  fun ppComHead name (r, r') = 
    seq [text name, Atomic.braces @@ seq [ppParam r, text "~>", ppParam r']]

  fun intersperse s xs = 
    case xs of 
       [] => []
     | [x] => [x]
     | x::xs => seq [x, s] :: intersperse s xs


  (* This is still quite rudimentary; we can learn to more interesting things like alignment, etc. *)

  fun ppTerm m = 
    case Abt.out m of 
       O.POLY (O.HYP_REF x) $ [] => seq [text ",", ppVar x]
     | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] =>
         hsep [Atomic.parens @@ hsep [ppVar x, Atomic.colon, ppTerm a], text "->", ppTerm bx]
     | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] =>
         hsep [Atomic.parens @@ hsep [ppVar x, Atomic.colon, ppTerm a], text "*", ppTerm bx]
     | O.MONO O.AP $ [_ \ m, _ \ n] => 
         Atomic.parens @@ expr @@ hvsep [ppTerm m, ppTerm n]
     | O.MONO O.PAIR $ [_ \ m, _ \ n] => 
         collection (char #"<") (char #">") Atomic.comma [ppTerm m, ppTerm n]
     | O.POLY (O.LOOP r) $ _ => 
         seq [text "loop", Atomic.squares @@ ppParam r]
     | O.POLY (O.PATH_AP r) $ [_ \ m] =>
         Atomic.parens @@ expr @@ hvsep [text "@", ppTerm m, ppParam r]
     | `x => ppVar x
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

     | x $# (ps, ms) =>
         seq
           [char #"#",text (Abt.Metavar.toString x),
            unlessEmpty ps @@ collection (char #"{") (char #"}") Atomic.comma @@ List.map (ppParam o #1) ps,
            unlessEmpty ms @@ collection (char #"[") (char #"]") Atomic.comma @@ List.map ppTerm ms]

  and ppTubes (eqs, tubes) = 
    expr @@ hvsep @@
      ListPair.map 
        (fn ((r1, r2), ([u], _) \ mx) => 
          Atomic.squares @@ hsep
            [seq [ppParam r1, Atomic.equals, ppParam r2],
              text "->",
              nest 1 @@ hvsep [Atomic.braces (text (Sym.toString u)), ppTerm mx]])
        (eqs, tubes)

  
  and ppBinder ((us, xs) \ m) = 
    case (us, xs) of 
        ([], []) => atLevel 10 @@ ppTerm m
      | _ => grouped @@ hvsep [seq [symBinding us, varBinding xs], align @@ ppTerm m] 

  and symBinding us =
    unlessEmpty us @@
      Atomic.braces @@ 
        hsep @@ intersperse Atomic.comma @@ List.map (text o Sym.toString) us

  and varBinding xs =
    unlessEmpty xs @@
      Atomic.squares @@ 
        hsep @@ intersperse Atomic.comma @@ List.map ppVar xs


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
