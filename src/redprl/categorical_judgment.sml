structure RedPrlCategoricalJudgment :
sig
  datatype 'a redprl_jdg =
     EQ of ('a * 'a) * 'a
   | TRUE of 'a
   | EQ_TYPE of 'a * 'a
   | SYNTH of 'a
   | CEQUIV of 'a * 'a

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
   | CEQUIV of 'a * 'a

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
     | CEQUIV (m, n) => CEQUIV (f m, f n)

  structure O = RedPrlOpData
  structure Tm = RedPrlAbt

  val synthesis =
    fn EQ _ => O.TRIV
     | TRUE _ => O.EXP
     | EQ_TYPE _ => O.TRIV
     | SYNTH _ => O.EXP
     | CEQUIV _ => O.TRIV

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
       | CEQUIV (m, n) => O.MONO O.JDG_CEQ $$ [([],[]) \ m, ([],[]) \ n]

    fun fromAbt jdg =
      case RedPrlAbt.out jdg of
         O.MONO O.JDG_EQ $ [_ \ m, _\ n, _ \ a] => EQ ((m, n), a)
       | O.MONO O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.MONO O.JDG_EQ_TYPE $ [_ \ m, _\ n] => EQ_TYPE (m, n)
       | O.MONO O.JDG_SYNTH $ [_ \ m] => SYNTH m
       | O.MONO O.JDG_CEQ $ [_ \ m, _ \ n] => CEQUIV (m, n)
       | _ => raise InvalidJudgment
  end

  val toString = TermPrinter.toString o toAbt
  val metactx = RedPrlAbt.metactx o toAbt

  fun pretty f =
    fn EQ ((m, n), a) => PP.concat [PP.text (f m), PP.text " = ", PP.text (f n), PP.text " in ", PP.text (f a)]
     | TRUE a => PP.concat [PP.text (f a), PP.text " true"]
     | EQ_TYPE (a, b) => PP.concat [PP.text (f a), PP.text " = ", PP.text (f b), PP.text " type"]
     | SYNTH m => PP.concat [PP.text (f m), PP.text " synth"]
     | CEQUIV (m, n) => PP.concat [PP.text (f m), PP.text " ~ ", PP.text (f n)]

  fun unify (j1, j2) =
    RedPrlAbt.Unify.unify (toAbt j1, toAbt j2)

  fun eq (j1, j2) =
    RedPrlAbt.eq (toAbt j1, toAbt j2)
end
