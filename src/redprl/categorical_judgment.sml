structure RedPrlCategoricalJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlCategoricalJudgmentData

  fun MEM (m, (a, l, k)) =
    EQ ((m, m), (a, l, k))

  fun TYPE (a, l, k) =
    EQ_TYPE ((a, a), l, k)

  fun SUB_UNIVERSE (a, l, k) =
    EQ_SUB_UNIVERSE ((a, a), l, k)

  fun map' f g h =
    fn EQ ((m, n), (a, l, k)) => EQ ((h m, h n), (h a, g l, k))
     | TRUE (a, l, k) => TRUE (h a, g l, k)
     | EQ_TYPE ((a, b), l, k) => EQ_TYPE ((h a, h b), g l, k)
     | EQ_SUB_UNIVERSE ((u, v), l, k) => EQ_SUB_UNIVERSE ((h u, h v), g l, k)
     | SYNTH (a, l, k) => SYNTH (h a, g l, k)
     | TERM tau => TERM tau
     | PARAM_SUBST (psi, m, tau) => PARAM_SUBST
         (List.map (fn (r, sigma, u) => (h r, sigma, f u)) psi, h m, tau)
  
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
       | EQ_SUB_UNIVERSE ((a, b), l, k) => expr @@ hvsep @@ List.concat
           [ if eq (a, b) then [h a] else [h a, Atomic.equals, h b]
           , [text "<="]
           , [Atomic.parens @@ expr @@ hsep @@ List.concat
               [ [Fpp.text "U"]
               , case l of NONE => [text "omega"] | SOME l => [g l]
               , if k = RedPrlKind.top then [] else [TermPrinter.ppKind k]
               ]]
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
     | EQ_SUB_UNIVERSE _ => O.TRIV
     | SYNTH _ => O.EXP
     | TERM tau => tau
     | PARAM_SUBST (_, _, tau) => tau

  local
    open RedPrlAbt
    structure L = RedPrlLevel
    structure O = RedPrlOpData
    infix $ $$ \
  in
    type jdg = (Sym.t, L.P.level, abt) jdg'

    val into : jdg -> abt =
      fn EQ ((m, n), (a, l, k)) => O.POLY (O.JDG_EQ (L.P.into l, k)) $$ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | TRUE (a, l, k) => O.POLY (O.JDG_TRUE (L.P.into l, k)) $$ [([],[]) \ a]
       | EQ_TYPE ((a, b), l, k) => O.POLY (O.JDG_EQ_TYPE (L.P.into l, k)) $$ [([],[]) \ a, ([],[]) \ b]
       | EQ_SUB_UNIVERSE ((u, v), l, k) => O.POLY (O.JDG_EQ_SUB_UNIVERSE (L.P.into l, k)) $$ [([],[]) \ u, ([],[]) \ v]
       | SYNTH (m, l, k) => O.POLY (O.JDG_SYNTH (L.P.into l, k)) $$ [([],[]) \ m]
       | TERM tau => O.MONO (O.JDG_TERM tau) $$ []
       | PARAM_SUBST (psi, m, tau) =>
         let
           val (rs, us) = ListPair.unzip (List.map (fn (r, sigma, u) => ((r, sigma), u)) psi)
           val (rs, sigmas) = ListPair.unzip rs
         in
           O.MONO (O.JDG_PARAM_SUBST (sigmas, tau)) $$ List.map (fn r => ([],[]) \ r) rs @ [(us,[]) \ m]
         end

    fun out jdg =
      case RedPrlAbt.out jdg of
         O.POLY (O.JDG_EQ (l, k)) $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, L.P.out l, k))
       | O.POLY (O.JDG_TRUE (l, k)) $ [_ \ a] => TRUE (a, L.P.out l, k)
       | O.POLY (O.JDG_EQ_TYPE (l, k)) $ [_ \ a, _ \ b] => EQ_TYPE ((a, b), L.P.out l, k)
       | O.POLY (O.JDG_EQ_SUB_UNIVERSE (l, k)) $ [_ \ u, _ \ v] => EQ_SUB_UNIVERSE ((u, v), L.P.out l, k)
       | O.POLY (O.JDG_SYNTH (l, k)) $ [_ \ m] => SYNTH (m, L.P.out l, k)
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

  local
    open RedPrlAst
    structure L = RedPrlAstLevel
    structure O = RedPrlOpData
    infix $ \
  in
    type astjdg = (string, L.P.level, ast) jdg'

    fun astOut jdg =
      case RedPrlAst.out jdg of
         O.POLY (O.JDG_EQ (l, k)) $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, L.P.out l, k))
       | O.POLY (O.JDG_TRUE (l, k)) $ [_ \ a] => TRUE (a, L.P.out l, k)
       | O.POLY (O.JDG_EQ_TYPE (l, k)) $ [_ \ m, _ \ n] => EQ_TYPE ((m, n), L.P.out l, k)
       | O.POLY (O.JDG_SYNTH (l, k)) $ [_ \ m] => SYNTH (m, L.P.out l, k)
       | O.MONO (O.JDG_TERM tau) $ [] => TERM tau
       | O.MONO (O.JDG_PARAM_SUBST (sigmas, tau)) $ args =>
         let
           val (us , _) \ m = List.last args
           val rs = List.map (fn _ \ r => r) (ListUtil.init args)
           val psi = ListPair.mapEq (fn ((r, sigma), u) => (r, sigma, u)) (ListPair.zipEq (rs, sigmas), us)
         in
           PARAM_SUBST (psi, m, tau)
         end
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment"]
  end
end
