structure RedPrlAtomicJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlAtomicJudgmentData
  type abt = RedPrlAbt.abt

  fun MEM (m, (a, l, k)) =
    EQ ((m, m), (a, l, k))

  fun TYPE (a, l, k) =
    EQ_TYPE ((a, a), l, k)

  fun map f =
    fn EQ ((m, n), (a, l, k)) => EQ ((f m, f n), (f a, RedPrlLevel.map f l, k))
     | TRUE (a, l, k) => TRUE (f a, RedPrlLevel.map f l, k)
     | EQ_TYPE ((a, b), l, k) => EQ_TYPE ((f a, f b), RedPrlLevel.map f l, k)
     | SUB_UNIVERSE (u, l, k) => SUB_UNIVERSE (f u, RedPrlLevel.map f l, k)
     | SYNTH (a, l, k) => SYNTH (f a, RedPrlLevel.map f l, k)
     | TERM tau => TERM tau

  fun @@ (f, x) = f x
  infixr @@

  local
    open Fpp
  in
    val pretty =
      fn EQ ((m, n), (a, l, k)) => expr @@ hvsep @@ List.concat
           [ if RedPrlAbt.eq (m, n) then [TermPrinter.ppTerm m]
             else [TermPrinter.ppTerm m, Atomic.equals, TermPrinter.ppTerm n]
           , [hsep [text "in", TermPrinter.ppTerm a]]
           , if RedPrlLevel.eq (l, RedPrlLevel.top) then []
             else [hsep [text "at", RedPrlLevel.pretty l]]
           , if k = RedPrlKind.top then []
             else [hsep [text "with", TermPrinter.ppKind k]]
           ]
       | TRUE (a, l, k) => expr @@ hvsep @@ List.concat
           [ [TermPrinter.ppTerm a]
           , if RedPrlLevel.eq (l, RedPrlLevel.top) then []
             else [hsep [text "at", RedPrlLevel.pretty l]]
           , if k = RedPrlKind.top then []
             else [hsep [text "with", TermPrinter.ppKind k]]
           ]
       | EQ_TYPE ((a, b), l, k) => expr @@ hvsep @@ List.concat
           [ if RedPrlAbt.eq (a, b) then [TermPrinter.ppTerm a]
             else [TermPrinter.ppTerm a, Atomic.equals, TermPrinter.ppTerm b]
           , if k = RedPrlKind.top
             then [hsep [text "type"]]
             else [hsep [TermPrinter.ppKind k, text "type"]]
           , if RedPrlLevel.eq (l, RedPrlLevel.top) then []
             else [hsep [text "at", RedPrlLevel.pretty l]]
           ]
       | SUB_UNIVERSE (u, l, k) => expr @@ hvsep
           [ TermPrinter.ppTerm u
           , text "<="
           , Atomic.parens @@ expr @@ hsep
               [ text "U"
               , RedPrlLevel.pretty l
               , if k = RedPrlKind.top then empty else TermPrinter.ppKind k
               ]
           ]
       | SYNTH (m, l, k) => expr @@ hvsep @@ List.concat
           [ [TermPrinter.ppTerm m, text "synth"]
           , if RedPrlLevel.eq (l, RedPrlLevel.top) then []
             else [hsep [text "at", RedPrlLevel.pretty l]]
           , if k = RedPrlKind.top then []
             else [hsep [hsep [text "with", TermPrinter.ppKind k]]]
           ]
       | TERM tau => TermPrinter.ppSort tau
  end

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRV
     | SUB_UNIVERSE _ => O.TRV
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
      fn EQ ((m, n), (a, l, k)) => O.JDG_EQ $$ [[] \ L.into l, [] \ kconst k, [] \ m, [] \ n, [] \ a]
       | TRUE (a, l, k) => O.JDG_TRUE $$ [[] \ L.into l, [] \ kconst k, [] \ a]
       | EQ_TYPE ((a, b), l, k) => O.JDG_EQ_TYPE $$ [[] \ L.into l, [] \ kconst k, [] \ a, [] \ b]
       | SUB_UNIVERSE (u, l, k) => O.JDG_SUB_UNIVERSE $$ [[] \ L.into l, [] \ kconst k, [] \ u]
       | SYNTH (m, l, k) => O.JDG_SYNTH $$ [[] \ L.into l, [] \ kconst k, [] \ m]

       | TERM tau => O.JDG_TERM tau $$ []

    fun outk kexpr = 
      case RedPrlAbt.out kexpr of
         O.KCONST k $ _ => k
       | _ => raise RedPrlError.error [Fpp.text "Invalid kind expression"]

    fun out jdg =
      case RedPrlAbt.out jdg of
         O.JDG_EQ $ [_ \ l, _ \ k, _ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, L.out l, outk k))
       | O.JDG_TRUE $ [_ \ l, _ \ k, _ \ a] => TRUE (a, L.out l, outk k)
       | O.JDG_EQ_TYPE $ [_ \ l, _ \ k, _ \ a, _ \ b] => EQ_TYPE ((a, b), L.out l, outk k)
       | O.JDG_SUB_UNIVERSE $ [_ \ l, _ \ k, _ \ u] => SUB_UNIVERSE (u, L.out l, outk k)
       | O.JDG_SYNTH $ [_ \ l, _ \ k, _ \ m] => SYNTH (m, L.out l, outk k)

       | O.JDG_TERM tau $ [] => TERM tau
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]

    val eq = fn (j1, j2) => eq (into j1, into j2)
  end
end
