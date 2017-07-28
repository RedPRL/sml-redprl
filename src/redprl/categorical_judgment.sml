structure RedPrlCategoricalJudgment :
sig
  datatype ('sym, 'a) redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of 'a * 'a
   | SYNTH of 'a
   | TERM of RedPrlSort.t
   | PARAM_SUBST of ('a * RedPrlParamSort.t * 'sym) list * 'a * RedPrlSort.t

  val MEM : 'a * 'a -> ('sym, 'a) redprl_jdg
  val TYPE : 'a -> ('sym, 'a) redprl_jdg

  val fromAst : RedPrlAst.ast -> (string, RedPrlAst.ast) redprl_jdg

  include CATEGORICAL_JUDGMENT where type ('sym, 'a) jdg = ('sym, 'a) redprl_jdg
end =
struct
  datatype ('sym, 'a) redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of 'a * 'a
   | SYNTH of 'a
   | TERM of RedPrlSort.t
   | PARAM_SUBST of ('a * RedPrlParamSort.t * 'sym) list * 'a * RedPrlSort.t

  fun MEM (m, a) =
    EQ ((m, m), a)

  fun TYPE a =
    EQ_TYPE (a, a)

  type ('sym, 'a) jdg = ('sym, 'a) redprl_jdg

  fun map sym f =
    fn EQ ((m, n), a) => EQ ((f m, f n), f a)
     | TRUE a => TRUE (f a)
     | EQ_TYPE (a, b) => EQ_TYPE (f a, f b)
     | SYNTH a => SYNTH (f a)
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
     | PARAM_SUBST (_, m, tau) => tau

  local
    open Tm
    structure O = RedPrlOpData
    infix $ $$ \
  in
    type abt = abt
    type sort = sort

    val toAbt : (Sym.t, abt) jdg -> abt =
      fn EQ ((m, n), a) => O.MONO O.JDG_EQ $$ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | TRUE a => O.MONO O.JDG_TRUE $$ [([],[]) \ a]
       | EQ_TYPE (a, b) => O.MONO O.JDG_EQ_TYPE $$ [([],[]) \ a, ([],[]) \ b]
       | SYNTH m => O.MONO O.JDG_SYNTH $$ [([],[]) \ m]
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
         O.MONO O.JDG_EQ $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), a)
       | O.MONO O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.MONO O.JDG_EQ_TYPE $ [_ \ m, _ \ n] => EQ_TYPE (m, n)
       | O.MONO O.JDG_SYNTH $ [_ \ m] => SYNTH m
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
         O.MONO O.JDG_EQ $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), a)
       | O.MONO O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.MONO O.JDG_EQ_TYPE $ [_ \ m, _ \ n] => EQ_TYPE (m, n)
       | O.MONO O.JDG_SYNTH $ [_ \ m] => SYNTH m
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

  fun pretty eq f =
    fn EQ ((m, n), a) =>
         if eq (m, n)
         then Fpp.expr (Fpp.hvsep [f m, Fpp.hsep [Fpp.text "in", f a]])
         else Fpp.expr (Fpp.hvsep [f m, Fpp.Atomic.equals, f n, Fpp.hsep [Fpp.text "in", f a]])
     | TRUE a => f a
     | EQ_TYPE (a, b) =>
         if eq (a, b)
         then Fpp.expr (Fpp.hvsep [f a, Fpp.text "type"])
         else Fpp.expr (Fpp.hvsep [f a, Fpp.Atomic.equals, f b, Fpp.text "type"])
     | SYNTH m => Fpp.expr (Fpp.hvsep [f m, Fpp.text "synth"])
     | TERM tau => TermPrinter.ppSort tau
     | PARAM_SUBST _ => Fpp.text "param-subst" (* TODO *)
  fun pretty' f = pretty (fn _ => false) f

  fun eq (j1, j2) =
    RedPrlAbt.eq (toAbt j1, toAbt j2)
end
