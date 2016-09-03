structure CategoricalJudgment : CATEGORICAL_JUDGMENT =
struct
  datatype 'a jdg =
     EQ of ('a * 'a) * 'a
   | MEM of 'a * 'a
   | TRUE of 'a
   | SYNTH of 'a
   | CEQUIV of 'a * 'a

  fun map f =
    fn EQ ((m, n), a) => EQ ((f m, f n), f a)
     | MEM (m, a) => MEM (f m, f a)
     | TRUE a => TRUE (f a)
     | SYNTH a => TRUE (f a)
     | CEQUIV (m, n) => CEQUIV (f m, f n)

  structure O = RedPrlOpData

  val synthesis =
    fn EQ _ => O.TRIV
     | MEM _ => O.TRIV
     | TRUE _ => O.EXP
     | SYNTH _ => O.EXP
     | CEQUIV _ => O.TRIV

  exception InvalidJudgment

  local
    open RedPrlAbt
    structure O = RedPrlOpData
    infix $ $$ \
  in
    type abt = abt
    type sort = sort

    val toAbt =
      fn EQ ((m, n), a) => O.MONO O.JDG_EQ $$ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a]
       | MEM (m, a) => O.MONO O.JDG_MEM $$ [([],[]) \ m, ([],[]) \ a]
       | TRUE a => O.MONO O.JDG_TRUE $$ [([],[]) \ a]
       | SYNTH m => O.MONO O.JDG_SYNTH $$ [([],[]) \ m]
       | CEQUIV (m, n) => O.MONO O.JDG_CEQ $$ [([],[]) \ m, ([],[]) \ n]

    fun fromAbt jdg =
      case RedPrlAbt.out jdg of
         O.MONO O.JDG_EQ $ [_ \ m, _\ n, _ \ a] => EQ ((m, n), a)
       | O.MONO O.JDG_MEM $ [_ \ m, _ \ a] => MEM (m, a)
       | O.MONO O.JDG_TRUE $ [_ \ a] => TRUE a
       | O.MONO O.JDG_SYNTH $ [_ \ m] => SYNTH m
       | O.MONO O.JDG_CEQ $ [_ \ m, _ \ n] => CEQUIV (m, n)
       | _ => raise InvalidJudgment



  end
end
