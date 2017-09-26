structure RedPrlAtomicJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlAtomicJudgmentData
  type abt = RedPrlAbt.abt
  type level = RedPrlLevel.P.level

  fun MEM (m, (a, l, k)) =
    EQ ((m, m), (a, l, k))

  fun TYPE (a, l, k) =
    EQ_TYPE ((a, a), l, k)

  fun map' f g h =
    fn EQ ((m, n), (a, l, k)) => EQ ((h m, h n), (h a, g l, k))
     | TRUE (a, l, k) => TRUE (h a, g l, k)
     | EQ_TYPE ((a, b), l, k) => EQ_TYPE ((h a, h b), g l, k)
     | SUB_UNIVERSE (u, l, k) => SUB_UNIVERSE (h u, g l, k)
     | SYNTH (a, l, k) => SYNTH (h a, g l, k)
     | TERM tau => TERM tau
     | PARAM_SUBST (psi, m, tau) => PARAM_SUBST (List.map (fn (r, sigma, u) => (h r, sigma, f u)) psi, h m, tau)
  
  fun map f = map' (fn x => x) (fn x => x) f

  fun @@ (f, x) = f x
  infixr @@

  local
    open Fpp
  in
    fun pretty' _ g h eq =
      fn EQ ((m, n), (a, l, k)) => expr @@ hvsep @@ List.concat
           [ if eq (m, n) then [h m] else [h m, Atomic.equals, h n]
           , [hsep [text "in", h a]]
           , case l of NONE => [] | SOME l => [hsep [text "at", g l]]
           , if k = RedPrlKind.top then []
             else [hsep [text "with", TermPrinter.ppKind k]]
           ]
       | TRUE (a, l, k) => expr @@ hvsep @@ List.concat
           [ [h a]
           , case l of NONE => [] | SOME l => [hsep [text "at", g l]]
           , if k = RedPrlKind.top then []
             else [hsep [text "with", TermPrinter.ppKind k]]
           ]
       | EQ_TYPE ((a, b), l, k) => expr @@ hvsep @@ List.concat
           [ if eq (a, b) then [h a] else [h a, Atomic.equals, h b]
           , if k = RedPrlKind.top
             then [hsep [text "type"]]
             else [hsep [TermPrinter.ppKind k, text "type"]]
           , case l of NONE => [] | SOME l => [hsep [text "at", g l]]
           ]
       | SUB_UNIVERSE (u, l, k) => expr @@ hvsep
           [ h u
           , text "<="
           , Atomic.parens @@ expr @@ hsep
               [ text "U"
               , case l of NONE => text "omega" | SOME l => g l
               , if k = RedPrlKind.top then empty else TermPrinter.ppKind k
               ]
           ]
       | SYNTH (m, l, k) => expr @@ hvsep @@ List.concat
           [ [h m, text "synth"]
           , case l of NONE => [] | SOME l => [hsep [text "at", g l]]
           , if k = RedPrlKind.top then []
             else [hsep [hsep [text "with", TermPrinter.ppKind k]]]
           ]
       | TERM tau => TermPrinter.ppSort tau
       | PARAM_SUBST _ => text "param-subst" (* TODO *)
  end

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRIV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRIV
     | SUB_UNIVERSE _ => O.TRIV
     | SYNTH _ => O.EXP
     | TERM tau => tau
     | PARAM_SUBST (_, _, tau) => tau

  local
    open RedPrlAbt
    structure L = RedPrlLevel
    structure O = RedPrlOpData
    infix $ $$ \
  in
    fun kconst k = 
      O.MONO (O.KCONST k) $$ []

    val into : jdg -> abt =
      fn EQ ((m, n), (a, SOME l, k)) => O.MONO (O.JDG_EQ true) $$ [([],[]) \ L.into l, ([],[]) \ kconst k, ([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | EQ ((m, n), (a, NONE, k)) => O.MONO (O.JDG_EQ false) $$ [([],[]) \ kconst k, ([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | TRUE (a, SOME l, k) => O.MONO (O.JDG_TRUE true) $$ [([],[]) \ L.into l, ([],[]) \ kconst k, ([],[]) \ a]
       | TRUE (a, NONE, k) => O.MONO (O.JDG_TRUE false) $$ [([],[]) \ kconst k, ([],[]) \ a]
       | EQ_TYPE ((a, b), SOME l, k) => O.MONO (O.JDG_EQ_TYPE true) $$ [([],[]) \ L.into l, ([],[]) \ kconst k, ([],[]) \ a, ([],[]) \ b]
       | EQ_TYPE ((a, b), NONE, k) => O.MONO (O.JDG_EQ_TYPE false) $$ [([],[]) \ kconst k, ([],[]) \ a, ([],[]) \ b]
       | SUB_UNIVERSE (u, SOME l, k) => O.MONO (O.JDG_SUB_UNIVERSE true) $$ [([],[]) \ L.into l, ([],[]) \ kconst k, ([],[]) \ u]
       | SUB_UNIVERSE (u, NONE, k) => O.MONO (O.JDG_SUB_UNIVERSE false) $$ [([],[]) \ kconst k, ([],[]) \ u]
       | SYNTH (m, SOME l, k) => O.MONO (O.JDG_SYNTH true) $$ [([],[]) \ L.into l, ([],[]) \ kconst k, ([],[]) \ m]
       | SYNTH (m, NONE, k) => O.MONO (O.JDG_SYNTH false) $$ [([],[]) \ kconst k, ([],[]) \ m]

       | TERM tau => O.MONO (O.JDG_TERM tau) $$ []
       | PARAM_SUBST (psi, m, tau) =>
         let
           val (rs, us) = ListPair.unzip (List.map (fn (r, sigma, u) => ((r, sigma), u)) psi)
           val (rs, sigmas) = ListPair.unzip rs
         in
           O.MONO (O.JDG_PARAM_SUBST (sigmas, tau)) $$ List.map (fn r => ([],[]) \ r) rs @ [(us,[]) \ m]
         end

    fun outk kexpr = 
      case RedPrlAbt.out kexpr of
         O.MONO (O.KCONST k) $ _ => k
       | _ => raise RedPrlError.error [Fpp.text "Invalid kind expression"]

    fun out jdg =
      case RedPrlAbt.out jdg of
         O.MONO (O.JDG_EQ true) $ [_ \ l, _ \ k, _ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, SOME (L.out l), outk k))
       | O.MONO (O.JDG_EQ false) $ [_ \ k, _ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, NONE, outk k))
       | O.MONO (O.JDG_TRUE true) $ [_ \ l, _ \ k, _ \ a] => TRUE (a, SOME (L.out l), outk k)
       | O.MONO (O.JDG_TRUE false) $ [_ \ k, _ \ a] => TRUE (a, NONE, outk k)
       | O.MONO (O.JDG_EQ_TYPE true) $ [_ \ l, _ \ k, _ \ a, _ \ b] => EQ_TYPE ((a, b), SOME (L.out l), outk k)
       | O.MONO (O.JDG_EQ_TYPE false) $ [_ \ k, _ \ a, _ \ b] => EQ_TYPE ((a, b), NONE, outk k)
       | O.MONO (O.JDG_SUB_UNIVERSE true) $ [_ \ l, _ \ k, _ \ u] => SUB_UNIVERSE (u, SOME (L.out l), outk k)
       | O.MONO (O.JDG_SUB_UNIVERSE false) $ [_ \ k, _ \ u] => SUB_UNIVERSE (u, NONE, outk k)
       | O.MONO (O.JDG_SYNTH true) $ [_ \ l, _ \ k, _ \ m] => SYNTH (m, SOME (L.out l), outk k)
       | O.MONO (O.JDG_SYNTH false) $ [_ \ k, _ \ m] => SYNTH (m, NONE, outk k)

       | O.MONO (O.JDG_TERM tau) $ [] => TERM tau
       | O.MONO (O.JDG_PARAM_SUBST (sigmas, tau)) $ args =>
         let
           val (us , _) \ m = List.last args
           val rs = List.map (fn _ \ r => r) (ListUtil.init args)
           val psi = ListPair.mapEq (fn ((r, sigma), u) => (r, sigma, u)) (ListPair.zipEq (rs, sigmas), us)
         in
           PARAM_SUBST (psi, m, tau)
         end
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]

    val pretty : jdg -> Fpp.doc = pretty'
      TermPrinter.ppSym L.pretty TermPrinter.ppTerm eq
    val eq = fn (j1, j2) => eq (into j1, into j2)
  end
end
