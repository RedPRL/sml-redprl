structure RedPrlAtomicJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlAtomicJudgmentData
  type abt = RedPrlAbt.abt

  fun MEM (m, a) =
    EQ ((m, m), a)

  fun map f =
    fn EQ ((m, n), a) => EQ ((f m, f n), f a)
     | TRUE a => TRUE (f a)
     | SYNTH a => SYNTH (f a)
     | TERM tau => TERM tau

  fun @@ (f, x) = f x
  infixr @@

  local
    open Fpp
  in
    val pretty =
      fn EQ ((m, n), a) => expr @@ hvsep @@ List.concat
           [ if RedPrlAbt.eq (m, n) then [TermPrinter.ppTerm m]
             else [TermPrinter.ppTerm m, Atomic.equals, TermPrinter.ppTerm n]
           , [hsep [text "in", TermPrinter.ppTerm a]]
           ]
       | TRUE a => TermPrinter.ppTerm a
       | SYNTH m => expr @@ hvsep @@ [TermPrinter.ppTerm m, text "synth"]
       | TERM tau => TermPrinter.ppSort tau
  end

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRV
     | TRUE _ => O.EXP
     | SYNTH _ => O.EXP
     | TERM tau => tau

  local
    open RedPrlAbt
    structure L = RedPrlLevel
    structure O = RedPrlOpData
    infix $ $$ \
  in
    fun kconst k = 
      O.KCONST k $$ []

    val into : jdg -> abt =
      fn EQ ((m, n), a) => O.JDG_EQ $$ [[] \ m, [] \ n, [] \ a]
       | TRUE a => O.JDG_TRUE $$ [[] \ a]
       | SYNTH m => O.JDG_SYNTH $$ [[] \ m]
       | TERM tau => O.JDG_TERM tau $$ []

    fun outk kexpr = 
      case RedPrlAbt.out kexpr of
         O.KCONST k $ _ => k
       | _ => raise RedPrlError.error [Fpp.text "Invalid kind expression"]

    fun out jdg =
      case RedPrlAbt.out jdg of
         O.JDG_EQ $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), a)
       | O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.JDG_SYNTH $ [_ \ m] => SYNTH m
       | O.JDG_TERM tau $ [] => TERM tau
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]

    val eq = fn (j1, j2) => eq (into j1, into j2)
  end
end
