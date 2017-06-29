structure RedPrlCategoricalJudgment :
sig
  datatype type_kind = KAN_TYPE | PRETYPE

  datatype 'a redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of type_kind * 'a * 'a
   | SYNTH of 'a
   | TERM of RedPrlSort.t

  val MEM : 'a * 'a -> 'a redprl_jdg
  val TYPE : type_kind * 'a -> 'a redprl_jdg

  include CATEGORICAL_JUDGMENT where type 'a jdg = 'a redprl_jdg
end =
struct
  datatype type_kind = KAN_TYPE | PRETYPE

  datatype 'a redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of type_kind * 'a * 'a
   | SYNTH of 'a
   | TERM of RedPrlSort.t

  fun MEM (m, a) =
    EQ ((m, m), a)

  fun TYPE (k, a) =
    EQ_TYPE (k, a, a)

  type 'a jdg = 'a redprl_jdg

  fun map f =
    fn EQ ((m, n), a) => EQ ((f m, f n), f a)
     | TRUE a => TRUE (f a)
     | EQ_TYPE (k, a, b) => EQ_TYPE (k, f a, f b)
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

    fun isKan KAN_TYPE = true
      | isKan _ = false

    val toAbt =
      fn EQ ((m, n), a) => O.MONO O.JDG_EQ $$ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | TRUE a => O.MONO O.JDG_TRUE $$ [([],[]) \ a]
       | EQ_TYPE (k, a, b) => O.MONO (O.JDG_EQ_TYPE (isKan k)) $$ [([],[]) \ a, ([],[]) \ b]
       | SYNTH m => O.MONO O.JDG_SYNTH $$ [([],[]) \ m]
       | TERM tau => O.MONO (O.JDG_TERM tau) $$ []

    fun fromAbt jdg =
      case RedPrlAbt.out jdg of
         O.MONO O.JDG_EQ $ [_ \ m, _\ n, _ \ a] => EQ ((m, n), a)
       | O.MONO O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.MONO (O.JDG_EQ_TYPE k) $ [_ \ m, _\ n] => EQ_TYPE (if k then KAN_TYPE else PRETYPE, m, n)
       | O.MONO O.JDG_SYNTH $ [_ \ m] => SYNTH m
       | O.MONO (O.JDG_TERM tau) $ [] => TERM tau
       | _ => raise InvalidJudgment
  end

  val metactx = RedPrlAbt.metactx o toAbt

  fun pretty f =
    fn EQ ((m, n), a) => Fpp.hsep [f m, Fpp.Atomic.equals, f n, Fpp.text "in", f a]
     | TRUE a => f a
     | EQ_TYPE (k, a, b) => Fpp.hsep [f a, Fpp.Atomic.equals, f b, if isKan k then Fpp.text "type" else Fpp.text "pretype"]
     | SYNTH m => Fpp.hsep [f m, Fpp.text "synth"]
     | TERM tau => TermPrinter.ppSort tau

  fun unify (j1, j2) =
    RedPrlAbt.Unify.unify (toAbt j1, toAbt j2)

  fun eq (j1, j2) =
    RedPrlAbt.eq (toAbt j1, toAbt j2)
end
