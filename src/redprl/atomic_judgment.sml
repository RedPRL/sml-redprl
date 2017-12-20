structure RedPrlAtomicJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlAtomicJudgmentData
  type abt = RedPrlAbt.abt

  fun MEM (m, a) =
    EQ ((m, m), a)

  fun TYPE (a, k) =
    EQ_TYPE ((a, a), k)

  fun map f =
    fn EQ ((m, n), a) => EQ ((f m, f n), f a)
     | TRUE a => TRUE (f a)
     | EQ_TYPE ((a, b), k) => EQ_TYPE ((f a, f b), k)
     | SUB_TYPE (a, b) => SUB_TYPE (f a, f b)
     | SUB_UNIVERSE (u, k) => SUB_UNIVERSE (f u, k)
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
       | EQ_TYPE ((a, b), k) => expr @@ hvsep @@ List.concat
           [ if RedPrlAbt.eq (a, b) then [TermPrinter.ppTerm a]
             else [TermPrinter.ppTerm a, Atomic.equals, TermPrinter.ppTerm b]
           , if k = RedPrlKind.top
             then [hsep [text "type"]]
             else [hsep [TermPrinter.ppKind k, text "type"]]
           ]
       | SUB_TYPE (a, b) => expr @@ hvsep
           [ TermPrinter.ppTerm a
           , text "<="
           , TermPrinter.ppTerm b
           , text "type"
           ]
       | SUB_UNIVERSE (u, k) => expr @@ hvsep
           [ TermPrinter.ppTerm u
           , text "<="
           , TermPrinter.ppKind k
           , text "universe"
           ]
       | SYNTH m => expr @@ hvsep
           [ TermPrinter.ppTerm m, text "synth"
           ]
       | TERM tau => TermPrinter.ppSort tau
  end

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRV
     | SUB_TYPE _ => O.TRV
     | SUB_UNIVERSE _ => O.TRV
     | SYNTH _ => O.EXP
     | TERM tau => tau

  structure E = RedPrlError

  val prettyAccessor = Fpp.text o O.accessorToStrung
  fun mapPart acc f jdg =
    case (jdg, acc) of
       (EQ ((m, n), a), O.AT_LEFT) => EQ ((f m, n), a)
     | (EQ ((m, n), a), O.AT_RIGHT) => EQ ((m, f n), a)
     | (EQ ((m, n), a), O.AT_TYPE) => EQ ((m, n), f a)
     | (EQ _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))
     | (TRUE a, O.AT_TOP) => TRUE (f a)
     | (TRUE a, O.AT_TYPE) => TRUE (f a)
     | (TRUE _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))
     | (EQ_TYPE ((a, b), k), O.AT_LEFT) => EQ_TYPE ((f a, b), k)
     | (EQ_TYPE ((a, b), k), O.AT_RIGHT) => EQ_TYPE ((a, f b), k)
     | (EQ_TYPE _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))
     | (SUB_TYPE (a, b), O.AT_LEFT) => SUB_TYPE (f a, b)
     | (SUB_TYPE (a, b), O.AT_RIGHT) => SUB_TYPE (a, f b)
     | (SUB_TYPE _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))
     | (SUB_UNIVERSE (u, k), O.AT_LEFT) => SUB_UNIVERSE (f u, k)
     | (SUB_UNIVERSE _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))
     | (SYNTH a, O.AT_TOP) => SYNTH (f a)
     | (SYNTH _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))
     | (TERM _, _) => E.raiseError (E.NOT_APPLICABLE (Fpp.text "mapPart", Fpp.hsep [pretty jdg, Fpp.text "at", prettyAccessor acc]))

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
       | EQ_TYPE ((a, b), k) => O.JDG_EQ_TYPE $$ [[] \ kconst k, [] \ a, [] \ b]
       | SUB_TYPE (a, b) => O.JDG_SUB_TYPE $$ [[] \ a, [] \ b]
       | SUB_UNIVERSE (u, k) => O.JDG_SUB_UNIVERSE $$ [[] \ kconst k, [] \ u]
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
       | O.JDG_EQ_TYPE $ [_ \ k, _ \ a, _ \ b] => EQ_TYPE ((a, b), outk k)
       | O.JDG_SUB_TYPE $ [_ \ a, _ \ b] => SUB_TYPE (a, b)
       | O.JDG_SUB_UNIVERSE $ [_ \ k, _ \ u] => SUB_UNIVERSE (u, outk k)
       | O.JDG_SYNTH $ [_ \ m] => SYNTH m

       | O.JDG_TERM tau $ [] => TERM tau
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]

    val eq = fn (j1, j2) => eq (into j1, into j2)
  end
end
