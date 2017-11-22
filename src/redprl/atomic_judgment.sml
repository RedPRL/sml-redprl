structure RedPrlAtomicJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlAtomicJudgmentData
  type abt = RedPrlAbt.abt

  fun MEM (m, (a, l)) =
    EQ ((m, m), (a, l))

  fun map f =
    fn EQ ((m, n), (a, l)) => EQ ((f m, f n), (f a, l))
     | TRUE (a, l) => TRUE (f a, l)
     | SUB_TYPE ((a, b), l) => SUB_TYPE ((f a, f b), l)
     | SYNTH (a, l) => SYNTH (f a, l)
     | TERM tau => TERM tau

  fun @@ (f, x) = f x
  infixr @@

  local
    open Fpp
  in
    val pretty =
      fn EQ ((m, n), (a, l)) => expr @@ hvsep @@ List.concat
           [ if RedPrlAbt.eq (m, n) then [TermPrinter.ppTerm m]
             else [TermPrinter.ppTerm m, Atomic.equals, TermPrinter.ppTerm n]
           , [hsep [text "in", TermPrinter.ppTerm a]]
           , [hsep [text "at", RedPrlLevel.pretty l]]
           ]
       | TRUE (a, l) => expr @@ hvsep
           [ TermPrinter.ppTerm a
           , hsep [text "at", RedPrlLevel.pretty l]
           ]
       | SUB_TYPE ((a, b), l) => expr @@ hvsep
           [ TermPrinter.ppTerm a
           , text "<="
           , TermPrinter.ppTerm b
           , hsep [text "at", RedPrlLevel.pretty l]
           ]
       | SYNTH (m, l) => expr @@ hvsep
           [ TermPrinter.ppTerm m, text "synth"
           , hsep [text "at", RedPrlLevel.pretty l]
           ]
       | TERM tau => TermPrinter.ppSort tau
  end

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRV
     | TRUE _ => O.EXP
     | SUB_TYPE _ => O.TRV
     | SYNTH _ => O.EXP
     | TERM tau => tau

  local
    open RedPrlAbt
    structure L = RedPrlLevel
    structure O = RedPrlOpData
    infix $ $$ \
  in
    val into : jdg -> abt =
      fn EQ ((m, n), (a, l)) => O.JDG_EQ $$ [[] \ L.into l, [] \ m, [] \ n, [] \ a]
       | TRUE (a, l) => O.JDG_TRUE $$ [[] \ L.into l, [] \ a]
       | SUB_TYPE ((a, b), l) => O.JDG_SUB_TYPE $$ [[] \ L.into l, [] \ a, [] \ b]
       | SYNTH (m, l) => O.JDG_SYNTH $$ [[] \ L.into l, [] \ m]

       | TERM tau => O.JDG_TERM tau $$ []

    fun out jdg =
      case RedPrlAbt.out jdg of
         O.JDG_EQ $ [_ \ l, _ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, L.out l))
       | O.JDG_TRUE $ [_ \ l, _ \ a] => TRUE (a, L.out l)
       | O.JDG_SUB_TYPE $ [_ \ l, _ \ a, _ \ b] => SUB_TYPE ((a, b), L.out l)
       | O.JDG_SYNTH $ [_ \ l, _ \ m] => SYNTH (m, L.out l)

       | O.JDG_TERM tau $ [] => TERM tau
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]

    val eq = fn (j1, j2) => eq (into j1, into j2)
  end
end
