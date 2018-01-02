structure AtomicJudgment : ATOMIC_JUDGMENT =
struct
  open AtomicJudgmentData
  type abt = RedPrlAbt.abt

  fun EQ ((m, n), a) =
    TRUE (SyntaxView.intoEq (a, m, n))

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
     | EQ_TYPE _ => O.EXP
     | SUB_TYPE _ => O.EXP
     | SUB_KIND _ => O.EXP
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
    structure V = Variance and A = Accessor and Syn = SyntaxView
  in
    fun lookupAccessor acc jdg =
      case (jdg, acc) of
         (TRUE ty, A.WHOLE) => ty
       | (TRUE ty, _) =>
           (case (Syn.out ty, acc) of
              (Syn.EQUALITY (ty, _, _), A.PART_TYPE) => ty
            | (Syn.EQUALITY (_, m, _), A.PART_LEFT) => m
            | (Syn.EQUALITY (_, _, n), A.PART_RIGHT) => n
            | _ =>
                RedPrlError.raiseError
                  (RedPrlError.NOT_APPLICABLE
                    (Fpp.text "lookupAccessor",
                     Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg])))
       | (EQ_TYPE ((m, _), _), A.PART_LEFT) => m
       | (EQ_TYPE ((_, n), _), A.PART_RIGHT) => n
       | (SUB_TYPE (m, _), A.PART_LEFT) => m
       | (SUB_TYPE (_, n), A.PART_RIGHT) => n
       | (SUB_KIND (m, _), A.PART_LEFT) => m
       | (SYNTH m, A.WHOLE) => m
       | _ =>
           RedPrlError.raiseError
             (RedPrlError.NOT_APPLICABLE
               (Fpp.text "lookupAccessor",
                Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg]))
    
    fun mapAccessor acc f jdg =
      case (jdg, acc) of
         (TRUE ty, A.WHOLE) => TRUE (f ty)
       | (TRUE ty, _) =>
           (case (Syn.out ty, acc) of
              (Syn.EQUALITY (ty, m, n), A.PART_TYPE) => TRUE (Syn.intoEq (f ty, m, n))
            | (Syn.EQUALITY (ty, m, n), A.PART_LEFT) => TRUE (Syn.intoEq (ty, f m, n))
            | (Syn.EQUALITY (ty, m, n), A.PART_RIGHT) => TRUE (Syn.intoEq (ty, m, f n))
            | _ =>
                RedPrlError.raiseError
                  (RedPrlError.NOT_APPLICABLE
                    (Fpp.text "mapAccessor",
                     Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg])))
       | (EQ_TYPE ((m, n), k), A.PART_LEFT) => EQ_TYPE ((f m, n), k)
       | (EQ_TYPE ((m, n), k), A.PART_RIGHT) => EQ_TYPE ((m, f n), k)
       | (SUB_TYPE (m, n), A.PART_LEFT) => SUB_TYPE (f m, n)
       | (SUB_TYPE (m, n), A.PART_RIGHT) => SUB_TYPE (m, f n)
       | (SUB_KIND (m, k), A.PART_LEFT) => SUB_KIND (f m, k)
       | (SYNTH m, A.WHOLE) => SYNTH (f m)
       | _ =>
           RedPrlError.raiseError
             (RedPrlError.NOT_APPLICABLE
               (Fpp.text "mapAccessor",
                Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg]))

    fun multiMapAccessor accs f jdg =
      List.foldl (fn (acc, state) => mapAccessor acc f state) jdg accs

    val variance =
      fn (TRUE _, A.WHOLE) => V.COVAR
       | (jdg as TRUE ty, acc) =>
           (case Syn.out ty of
              Syn.EQUALITY _ =>
                (case acc of
                   A.PART_TYPE => V.COVAR
                 | A.PART_LEFT => V.ANTIVAR
                 | A.PART_RIGHT => V.ANTIVAR
                 | A.WHOLE => RedPrlError.raiseError (RedPrlError.IMPOSSIBLE (Fpp.text "impossible cases in variance")))
            | _ =>
                RedPrlError.raiseError
                  (RedPrlError.NOT_APPLICABLE
                    (Fpp.text "variance",
                     Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg])))
       | (EQ_TYPE _, A.PART_LEFT) => V.ANTIVAR
       | (EQ_TYPE _, A.PART_RIGHT) => V.ANTIVAR
       | (SUB_TYPE _, A.PART_LEFT) => V.CONTRAVAR
       | (SUB_TYPE _, A.PART_RIGHT) => V.COVAR
       | (SUB_KIND _, A.PART_LEFT) => V.CONTRAVAR
       | (SYNTH _, A.WHOLE) => V.ANTIVAR
       | (jdg, acc) =>
           RedPrlError.raiseError
             (RedPrlError.NOT_APPLICABLE
               (Fpp.text "variance",
                Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg]))

    structure View =
    struct
      val matchAsTrue =
        fn TRUE ty => ty

      val matchTrueAsEq =
        fn TRUE ty => (case Syn.out ty of Syn.EQUALITY (ty, m, n) => ((m, n), ty))
      
      val makeEqAsTrue = EQ
  
      datatype as_level = FINITE of RedPrlLevel.t | OMEGA
  
      val matchAsEqType =
        fn jdg as TRUE ty =>
             (case Syn.out ty of
                Syn.EQUALITY (univ, a, b) =>
                  let
                    val Syn.UNIVERSE (l, k) = Syn.out univ
                  in
                    ((a, b), FINITE l, k)
                  end
              | _ => RedPrlError.raiseError @@ RedPrlError.NOT_APPLICABLE (Fpp.text "matchAsEqType", pretty jdg))
         | EQ_TYPE ((a, b), k) => ((a, b), OMEGA, k)
         | jdg => RedPrlError.raiseError @@ RedPrlError.NOT_APPLICABLE (Fpp.text "matchAsEqType", pretty jdg)
         
      val makeAsEqType =
        fn ((a, b), OMEGA, k) => EQ_TYPE ((a, b), k)
         | ((a, b), FINITE l, k) => EQ ((a, b), Syn.intoU (l, k))
   
      datatype as_type = INTERNAL_TYPE of abt | UNIV_OMEGA of RedPrlKind.t
   
      val matchAsEq =
        fn TRUE ty => (case Syn.out ty of Syn.EQUALITY (ty, m, n) => ((m, n), INTERNAL_TYPE ty))
         | EQ_TYPE ((a, b), k) => ((a, b), UNIV_OMEGA k)
         | jdg => RedPrlError.raiseError @@ RedPrlError.NOT_APPLICABLE (Fpp.text "matchAsEq", pretty jdg)
  
      val makeAsEq =
        fn ((a, b), INTERNAL_TYPE ty) => EQ ((a, b), ty)
         | ((a, b), UNIV_OMEGA k) => EQ_TYPE ((a, b), k)
  
      val makeAsMem =
        fn (a, INTERNAL_TYPE ty) => MEM (a, ty)
         | (a, UNIV_OMEGA k) => TYPE (a, k)
  
      val makeAsSubType =
        fn (a, INTERNAL_TYPE b) => SUB_TYPE (a, b)
         | (a, UNIV_OMEGA k) => SUB_KIND (a, k)

      val classifier =
        fn (TRUE _, A.WHOLE) => UNIV_OMEGA RedPrlKind.top
         | (jdg as TRUE ty, acc) =>
             (case Syn.out ty of
                Syn.EQUALITY (ty, _, _) =>
                  (case acc of
                     A.PART_TYPE => UNIV_OMEGA RedPrlKind.top
                   | A.PART_LEFT => INTERNAL_TYPE ty
                   | A.PART_RIGHT => INTERNAL_TYPE ty
                   | A.WHOLE => RedPrlError.raiseError (RedPrlError.IMPOSSIBLE (Fpp.text "impossible cases in classifier")))
              | _ =>
                  RedPrlError.raiseError
                    (RedPrlError.NOT_APPLICABLE
                      (Fpp.text "classifier",
                       Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg])))
         | (EQ_TYPE (_, k), A.PART_LEFT) => UNIV_OMEGA k
         | (EQ_TYPE (_, k), A.PART_RIGHT) => UNIV_OMEGA k
         | (SUB_TYPE _, A.PART_LEFT) => UNIV_OMEGA RedPrlKind.top
         | (SUB_TYPE _, A.PART_RIGHT) => UNIV_OMEGA RedPrlKind.top
         | (SUB_KIND _, A.PART_LEFT) => UNIV_OMEGA RedPrlKind.top
         | (jdg, acc) =>
             RedPrlError.raiseError
               (RedPrlError.NOT_APPLICABLE
                 (Fpp.text "classifier",
                  Fpp.hvsep [Fpp.hsep [A.pretty acc, Fpp.text "of"], pretty jdg]))
    end
  end
end
