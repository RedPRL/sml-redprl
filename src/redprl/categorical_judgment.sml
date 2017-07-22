structure RedPrlCategoricalJudgment :
sig
  type kind = RedPrlKind.t

  datatype ('sym, 'a) redprl_jdg =

   (* `EQ ((m, n), (a, k))`:
    *   `EQ_TYPE ((a, a), k)` and `m` and `n` are related by the PER associated with `a`.
    *   The realizer is `TV` of sort `TRIV`.
    *)
     EQ of ('a * 'a) * ('a * kind)

   (* `TRUE (a, k)`:
    *   `EQ_TYPE ((a, a), k)` and there exists a term `m` such that
    *   `EQ ((m, m), (a, k))` is provable.
    *   The realizer is such an `m` of sort `EXP`.
    *)
   | TRUE of 'a * kind

   (* `EQ_TYPE ((a, b), k)`:
    *   `a` and `b` are equal types, taking into account the additional
    *   structures specified by `k`. For example, `EQ_TYPE ((a, b), KAN)`
    *   means they are equally Kan, in addition to being equal pretypes.
    *   The realizer is `TV` of sort `TRIV`.
    *)
   | EQ_TYPE of ('a * 'a) * kind

   (* `TERM tau`:
    *   There exists some `m` of sort `tau`.
    *   The realizer is such an `m` of sort `tau`.
    *)
   | SYNTH of 'a * kind

   (* `TERM tau`:
    *   There exists some `m` of sort `tau`.
    *   The realizer is such an `m` of sort `tau`.
    *)
   | TERM of RedPrlSort.t

   | PARAM_SUBST of ('a * RedPrlParamSort.t * 'sym) list * 'a * RedPrlSort.t

  val MEM : 'a * ('a * kind) -> ('sym, 'a) redprl_jdg
  val TYPE : 'a * kind -> ('sym, 'a) redprl_jdg

  val fromAst : RedPrlAst.ast -> (string, RedPrlAst.ast) redprl_jdg

  include CATEGORICAL_JUDGMENT where type ('sym, 'a) jdg = ('sym, 'a) redprl_jdg
end =
struct
  type kind = RedPrlKind.t

  datatype ('sym, 'a) redprl_jdg =
     EQ of ('a * 'a) * ('a * kind)
   | TRUE of 'a * kind
   | EQ_TYPE of ('a * 'a) * kind
   | SYNTH of 'a * kind
   | TERM of RedPrlSort.t
   | PARAM_SUBST of ('a * RedPrlParamSort.t * 'sym) list * 'a * RedPrlSort.t

  fun MEM (m, (a, k)) =
    EQ ((m, m), (a, k))

  fun TYPE (a, k) =
    EQ_TYPE ((a, a), k)

  type ('sym, 'a) jdg = ('sym, 'a) redprl_jdg

  fun map sym f =
    fn EQ ((m, n), (a, k)) => EQ ((f m, f n), (f a, k))
     | TRUE (a, k) => TRUE (f a, k)
     | EQ_TYPE ((a, b), k) => EQ_TYPE ((f a, f b), k)
     | SYNTH (a, k) => SYNTH (f a, k)
     | TERM tau => TERM tau
     | PARAM_SUBST (psi, m, tau) => PARAM_SUBST (List.map (fn (r, sigma, u) => (f r, sigma, sym u)) psi, f m, tau) 
  
  fun map_ f = map (fn x => x) f

  structure O = RedPrlOpData
  structure Tm = RedPrlAbt
  structure Ast = RedPrlAst

  val synthesis =
    fn EQ _ => O.TRIV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRIV
     | SYNTH _ => O.EXP
     | TERM tau => tau
     | PARAM_SUBST (_, _, tau) => tau

  local
    open Tm
    structure O = RedPrlOpData
    infix $ $$ \
  in
    type abt = abt
    type sort = sort

    val toAbt : (Sym.t, abt) jdg -> abt =
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

    fun fromAbt jdg =
      case RedPrlAbt.out jdg of
         O.MONO (O.JDG_EQ k) $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, k))
       | O.MONO (O.JDG_TRUE k) $ [_ \ a] => TRUE (a, k)
       | O.MONO (O.JDG_EQ_TYPE k) $ [_ \ m, _ \ n] => EQ_TYPE ((m, n), k)
       | O.MONO (O.JDG_SYNTH k) $ [_ \ m] => SYNTH (m, k)
       | O.MONO (O.JDG_TERM tau) $ [] => TERM tau
       | O.MONO (O.JDG_PARAM_SUBST (sigmas, tau)) $ args =>
         let
           val ((us, _) \ m) :: args' = List.rev args
           val rs = List.rev (List.map (fn _ \ r => r) args')
           val psi = List.map (fn ((r, sigma), u) => (r, sigma, u)) (ListPair.zipEq (ListPair.zipEq (rs, sigmas), us))
         in
           PARAM_SUBST (psi, m, tau)
         end
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment:", TermPrinter.ppTerm jdg]
  end

  local
    open Ast
    structure O = RedPrlOpData
    infix $ \
  in
    fun fromAst jdg =
      case Ast.out jdg of
         O.MONO (O.JDG_EQ k) $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), (a, k))
       | O.MONO (O.JDG_TRUE k) $ [_ \ a] => TRUE (a, k)
       | O.MONO (O.JDG_EQ_TYPE k) $ [_ \ m, _ \ n] => EQ_TYPE ((m, n), k)
       | O.MONO (O.JDG_SYNTH k) $ [_ \ m] => SYNTH (m, k)
       | O.MONO (O.JDG_TERM tau) $ [] => TERM tau
       | O.MONO (O.JDG_PARAM_SUBST (sigmas, tau)) $ args =>
         let
           val ((us, _) \ m) :: args' = List.rev args
           val rs = List.rev (List.map (fn _ \ r => r) args')
           val psi = List.map (fn ((r, sigma), u) => (r, sigma, u)) (ListPair.zipEq (ListPair.zipEq (rs, sigmas), us))
         in
           PARAM_SUBST (psi, m, tau)
         end
       | _ => raise RedPrlError.error [Fpp.text "Invalid judgment"]
  end

  val metactx = RedPrlAbt.metactx o toAbt

  fun @@ (f, x) = f x
  infixr @@

  fun pretty eq f =
    fn EQ ((m, n), (a, k)) => Fpp.expr @@ Fpp.hvsep @@ List.concat
         [ if eq (m, n) then [f m] else [f m, Fpp.Atomic.equals, f n]
         , [Fpp.hsep [Fpp.text "in", f a]]
         , [Fpp.hsep [Fpp.text "with", TermPrinter.ppKind k]]
         ]
     | TRUE (a, k) => Fpp.expr @@ Fpp.hvsep
         [f a, Fpp.hsep [Fpp.text "with", TermPrinter.ppKind k]]
     | EQ_TYPE ((a, b), k) => Fpp.expr @@ Fpp.hvsep @@ List.concat
         [ if eq (a, b) then [f a] else [f a, Fpp.Atomic.equals, f b]
         , [Fpp.hsep [Fpp.text "type", Fpp.text "with", TermPrinter.ppKind k]]
         ]
     | SYNTH (m, k) => Fpp.expr @@ Fpp.hvsep
         [f m, Fpp.hsep [Fpp.text "synth", Fpp.text "with", TermPrinter.ppKind k]]
     | TERM tau => TermPrinter.ppSort tau
     | PARAM_SUBST _ => Fpp.text "param-subst" (* TODO *)
  fun pretty' f = pretty (fn _ => false) f

  fun eq (j1, j2) =
    RedPrlAbt.eq (toAbt j1, toAbt j2)
end
