structure AtomicJudgment : ATOMIC_JUDGMENT =
struct
  open AtomicJudgmentData
  type abt = RedPrlAbt.abt

  fun EQ ((m, n), a) =
    TRUE (SyntaxView.into (SyntaxView.EQUALITY (a, m, n)))

  fun MEM (m, a) =
    EQ ((m, m), a)

  fun TYPE (a, k) =
    EQ_TYPE ((a, a), k)

  fun map f =
    fn TRUE a => TRUE (f a)
     | EQ_TYPE ((a, b), k) => EQ_TYPE ((f a, f b), k)
     | SUB_TYPE (a, b) => SUB_TYPE (f a, f b)
     | SUB_KIND (u, k) => SUB_KIND (f u, k)
     | SYNTH a => SYNTH (f a)
     | TERM tau => TERM tau

  fun @@ (f, x) = f x
  infixr @@

  local
    open Fpp
  in
    val pretty =
      fn TRUE a => TermPrinter.ppTerm a
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
       | SUB_KIND (u, k) => expr @@ hvsep
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
    fn TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRV
     | SUB_TYPE _ => O.TRV
     | SUB_KIND _ => O.TRV
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
      fn TRUE a => O.JDG_TRUE $$ [[] \ a]
       | EQ_TYPE ((a, b), k) => O.JDG_EQ_TYPE $$ [[] \ kconst k, [] \ a, [] \ b]
       | SUB_TYPE (a, b) => O.JDG_SUB_TYPE $$ [[] \ a, [] \ b]
       | SUB_KIND (u, k) => O.JDG_SUB_KIND $$ [[] \ kconst k, [] \ u]
       | SYNTH m => O.JDG_SYNTH $$ [[] \ m]

       | TERM tau => O.JDG_TERM tau $$ []

    fun outk kexpr =
      case RedPrlAbt.out kexpr of
         O.KCONST k $ _ => k
       | _ => raise RedPrlError.error [Fpp.text "Invalid kind expression"]

    fun out jdg =
      case RedPrlAbt.out jdg of
         O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.JDG_EQ_TYPE $ [_ \ k, _ \ a, _ \ b] => EQ_TYPE ((a, b), outk k)
       | O.JDG_SUB_TYPE $ [_ \ a, _ \ b] => SUB_TYPE (a, b)
       | O.JDG_SUB_KIND $ [_ \ k, _ \ u] => SUB_KIND (u, outk k)
       | O.JDG_SYNTH $ [_ \ m] => SYNTH m

       | O.JDG_TERM tau $ [] => TERM tau
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]

    val eq = fn (j1, j2) => eq (into j1, into j2)
  end

  local
    structure V = Variance and A = Accessor
  in
    val variance =
      fn (TRUE _, A.WHOLE) => V.COVAR
       | (TRUE _, A.PART_TYPE) => V.COVAR
       | (TRUE _, A.PART_LEFT) => V.ANTIVAR
       | (TRUE _, A.PART_RIGHT) => V.ANTIVAR
       | (EQ_TYPE _, A.PART_LEFT) => V.ANTIVAR
       | (EQ_TYPE _, A.PART_RIGHT) => V.ANTIVAR
       | (SUB_TYPE _, A.PART_LEFT) => V.CONTRAVAR
       | (SUB_TYPE _, A.PART_RIGHT) => V.COVAR
       | (SUB_KIND _, A.PART_LEFT) => V.CONTRAVAR
       | (jdg, acc) =>
           RedPrlError.raiseError
             (RedPrlError.NOT_APPLICABLE
               (Fpp.text "variance",
                Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg]))
  end
end
