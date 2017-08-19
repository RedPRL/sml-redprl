structure RedPrlCategoricalJudgment : CATEGORICAL_JUDGMENT =
struct
  open RedPrlCategoricalJudgmentData

  fun MEM (m, (a, k)) =
    EQ ((m, m), (a, k))

  fun TYPE (a, k) =
    EQ_TYPE ((a, a), k)

  fun map' f g =
    fn EQ ((m, n), (a, k)) => EQ ((g m, g n), (g a, k))
     | TRUE (a, k) => TRUE (g a, k)
     | EQ_TYPE ((a, b), k) => EQ_TYPE ((g a, g b), k)
     | SYNTH (a, k) => SYNTH (g a, k)
     | TERM tau => TERM tau
     | PARAM_SUBST (psi, m, tau) => PARAM_SUBST
         (List.map (fn (r, sigma, u) => (g r, sigma, f u)) psi, g m, tau)
  
  fun map f = map' (fn x => x) f

  fun @@ (f, x) = f x
  infixr @@

  fun pretty' _ g eq =
    fn EQ ((m, n), (a, k)) => Fpp.expr @@ Fpp.hvsep @@ List.concat
         [ if eq (m, n) then [g m] else [g m, Fpp.Atomic.equals, g n]
         , [Fpp.hsep [Fpp.text "in", g a]]
         , if k = RedPrlKind.top then [] else [Fpp.hsep [Fpp.text "with", TermPrinter.ppKind k]]
         ]
     | TRUE (a, k) => Fpp.expr @@ Fpp.hvsep @@ List.concat
         [ [g a]
         , if k = RedPrlKind.top then []
           else [Fpp.hsep [Fpp.hsep [Fpp.text "with", TermPrinter.ppKind k]]]
         ]
     | EQ_TYPE ((a, b), k) => Fpp.expr @@ Fpp.hvsep @@ List.concat
         [ if eq (a, b) then [g a] else [g a, Fpp.Atomic.equals, g b]
         , if k = RedPrlKind.top
           then [Fpp.hsep [Fpp.text "type"]]
           else [Fpp.hsep [TermPrinter.ppKind k, Fpp.text "type"]]
         ]
     | SYNTH (m, k) => Fpp.expr @@ Fpp.hvsep @@ List.concat
         [ [g m, Fpp.text "synth"]
         , if k = RedPrlKind.top then []
           else [Fpp.hsep [Fpp.hsep [Fpp.text "with", TermPrinter.ppKind k]]]
         ]
     | TERM tau => TermPrinter.ppSort tau
     | PARAM_SUBST _ => Fpp.text "param-subst" (* TODO *)

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRIV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRIV
     | SYNTH _ => O.EXP
     | TERM tau => tau
     | PARAM_SUBST (_, _, tau) => tau

  local
    open RedPrlAbt
    structure O = RedPrlOpData
    infix $ $$ \
  in
    type jdg = (Sym.t, abt) jdg'

    val into : jdg -> abt =
      fn EQ ((m, n), (a, k)) => O.MONO (O.JDG_EQ k) $$ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | TRUE (a, k) => O.MONO (O.JDG_TRUE k) $$ [([],[]) \ a]
       | EQ_TYPE ((a, b), k) => O.MONO (O.JDG_EQ_TYPE k) $$ [([],[]) \ a, ([],[]) \ b]
       | SYNTH (m, k) => O.MONO (O.JDG_SYNTH k) $$ [([],[]) \ m]
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
         O.MONO (O.JDG_EQ k) $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, k))
       | O.MONO (O.JDG_TRUE k) $ [_ \ a] => TRUE (a, k)
       | O.MONO (O.JDG_EQ_TYPE k) $ [_ \ m, _ \ n] => EQ_TYPE ((m, n), k)
       | O.MONO (O.JDG_SYNTH k) $ [_ \ m] => SYNTH (m, k)
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

    val pretty : jdg -> Fpp.doc = pretty' TermPrinter.ppSym TermPrinter.ppTerm eq
    val eq = fn (j1, j2) => eq (into j1, into j2)
  end

  local
    open RedPrlAst
    structure O = RedPrlOpData
    infix $ \
  in
    type astjdg = (string, ast) jdg'

    fun astOut jdg =
      case RedPrlAst.out jdg of
         O.MONO (O.JDG_EQ k) $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, k))
       | O.MONO (O.JDG_TRUE k) $ [_ \ a] => TRUE (a, k)
       | O.MONO (O.JDG_EQ_TYPE k) $ [_ \ m, _ \ n] => EQ_TYPE ((m, n), k)
       | O.MONO (O.JDG_SYNTH k) $ [_ \ m] => SYNTH (m, k)
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
