structure RedPrlCategoricalJudgment :
sig
  datatype 'a redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of 'a * 'a
   | SYNTH of 'a
   | TERM of RedPrlSort.t

  val MEM : 'a * 'a -> 'a redprl_jdg
  val TYPE : 'a -> 'a redprl_jdg

  include CATEGORICAL_JUDGMENT where type 'a jdg = 'a redprl_jdg
end =
struct
  datatype 'a redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of 'a * 'a
   | SYNTH of 'a
   | TERM of RedPrlSort.t

  fun MEM (m, a) =
    EQ ((m, m), a)

  fun TYPE a =
    EQ_TYPE (a, a)

  type 'a jdg = 'a redprl_jdg

  fun map f =
    fn EQ ((m, n), a) => EQ ((f m, f n), f a)
     | TRUE a => TRUE (f a)
     | EQ_TYPE (a, b) => EQ_TYPE (f a, f b)
     | SYNTH a => SYNTH (f a)
     | TERM tau => TERM tau

  structure O = RedPrlOpData
  structure Tm = RedPrlAbt

  val synthesis =
    fn EQ _ => O.TRIV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRIV
     | SYNTH _ => O.EXP
     | TERM tau => tau

  exception InvalidJudgment

  local
    open Tm
    structure O = RedPrlOpData
    infix $ $$ \
  in
    type abt = abt
    type sort = sort

    val toAbt =
      fn EQ ((m, n), a) => O.MONO O.JDG_EQ $$ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | TRUE a => O.MONO O.JDG_TRUE $$ [([],[]) \ a]
       | EQ_TYPE (a, b) => O.MONO O.JDG_EQ_TYPE $$ [([],[]) \ a, ([],[]) \ b]
       | SYNTH m => O.MONO O.JDG_SYNTH $$ [([],[]) \ m]
       | TERM tau => O.MONO (O.JDG_TERM tau) $$ []

    fun fromAbt jdg =
      case RedPrlAbt.out jdg of
         O.MONO O.JDG_EQ $ [_ \ m, _ \ n, _ \ a] => EQ ((m, n), a)
       | O.MONO O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.MONO O.JDG_EQ_TYPE $ [_ \ m, _ \ n] => EQ_TYPE (m, n)
       | O.MONO O.JDG_SYNTH $ [_ \ m] => SYNTH m
       | O.MONO (O.JDG_TERM tau) $ [] => TERM tau
       | _ => raise InvalidJudgment
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
  fun pretty' f = pretty (fn _ => false) f

  fun unify (j1, j2) =
    RedPrlAbt.Unify.unify (toAbt j1, toAbt j2)

  fun eq (j1, j2) =
    RedPrlAbt.eq (toAbt j1, toAbt j2)
end
