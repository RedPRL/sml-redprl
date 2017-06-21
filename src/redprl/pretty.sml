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
end =
struct
  structure Abt = RedPrlAbt
  structure P = RedPrlParameterTerm

  open FppBasis Fpp Abt
  structure O = RedPrlOpData

  type t = Abt.abt

  fun >> (m, n) = Monad.bind m (fn _ => n)
  infix 2 >>

  fun @@ (f, x) = f x
  infix 0 $ $$ $# \
  infixr 0 @@

  val ppVar = text o Var.toString
  val ppParam = text o P.toString Sym.toString

  fun unlessEmpty xs m = 
    case xs of 
       [] => Monad.ret ()
     | _ => m

  (* This is still quite rudimentary; we can learn to more interesting things like alignment, etc. *)
  fun ppTerm m = 
    case Abt.out m of 
       O.POLY (O.HYP_REF x) $ [] => text "," >> ppVar x
     | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] =>
         hsep [Atomic.parens @@ hsep [ppVar x, Atomic.colon, ppTerm a], text "->", ppTerm bx]
     | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] =>
         hsep [Atomic.parens @@ hsep [ppVar x, Atomic.colon, ppTerm a], text "*", ppTerm bx]
     | O.MONO O.AP $ [_ \ m, _ \ n] => 
         app (ppTerm m) [ppTerm n]
     | O.MONO O.PAIR $ [_ \ m, _ \ n] => 
         collection (char #"<") (char #">") Atomic.comma [ppTerm m, ppTerm n]
     | O.MONO O.PATH_ABS $ [([x], _) \ m] =>
         hsep [char #"<" >> ppVar x >> char #">", ppTerm m]
     | O.POLY (O.LOOP r) $ _ => 
         text "loop" >> char #"[" >> ppParam r >> char #"]"
     | O.POLY (O.PATH_AP r) $ [_ \ m] =>
         inf 2 LEFT {opr = char #"@", arg1 = ppTerm m, arg2 = ppParam r}
     | `x => ppVar x
     | theta $ args => 
         text (RedPrlOperator.toString Sym.toString theta)
           >> unlessEmpty args (collection (char #"(") (char #")") (char #";") (List.map ppBinder args))
     | x $# (ps, ms) =>
         char #"#" >> text (Abt.Metavar.toString x) 
           >> unlessEmpty ps (collection (char #"{") (char #"}") Atomic.comma (List.map (ppParam o #1) ps))
           >> unlessEmpty ms (collection (char #"[") (char #"]") Atomic.comma (List.map ppTerm ms))
  
  and ppBinder (b \ m) = 
    ppBinding b >> ppTerm m

  and ppBinding (us, xs) = 
    case (us, xs) of 
       ([], []) => Monad.ret ()
     | _ => symBinding us >> varBinding xs >> char #"."
  
  and symBinding us =
    unlessEmpty us @@ 
      collection (char #"{") (char #"}") Atomic.comma (List.map (text o Sym.toString) us)

  and varBinding xs =
    unlessEmpty xs @@ 
      collection (char #"[") (char #"]") Atomic.comma (List.map ppVar xs)


  val toString = 
    FppRenderPlainText.toString 
      o FinalPrinter.execPP
      o ppTerm
end
