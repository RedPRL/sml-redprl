functor NominalLcfSemantics (M : NOMINAL_LCF_MODEL) : NOMINAL_LCF_SEMANTICS =
struct
  open M

  fun extendTactic (tac : tactic) : multitactic =
    fn alpha => Lcf.subst (fn _ => tac alpha)

  fun contractMultitactic (mtac : multitactic) : tactic =
    fn alpha => fn jdg =>
      let
        val x = Lcf.J.Tm.Metavariable.named "?x"
        val psi = Lcf.T.snoc Lcf.T.empty x jdg
      in
        mtac alpha (psi, fn rho => Lcf.T.lookup rho x)
      end

  structure MT = Multitacticals (Lcf)

  structure Seq =
  struct
    fun prepend us =
      let
        val n = List.length us
      in
        fn alpha => fn i =>
          if i < n then
            List.nth (us, i)
          else
            alpha (i + n)
      end

    fun bite n alpha =
      fn i =>
        alpha (i + n)

    fun probe (alpha : 'a seq) : 'a seq * int ref =
      let
        val mref = ref 0
        fun updateModulus i = if !mref < i then mref := i else ()
        fun beta i = (updateModulus (i + 1); alpha i)
      in
        (beta, mref)
      end
  end

  fun composeMultitactics mtacs =
    List.foldr
      (fn ((us : Syn.symbol list, mtac : multitactic), rest) => fn alpha => fn st =>
        let
          val beta = Seq.prepend us alpha
          val (beta', modulus) = Seq.probe (Seq.prepend us beta)
          val st' = mtac beta' st
        in
          rest (Seq.bite (!modulus) beta) st'
        end)
      (fn _ => fn st => st)
      mtacs

  local
    open Syn
  in
    fun statement (sign, rho) stmt =
      case Stmt.out sign stmt of
           Stmt.SEQ bindings =>
             let
               fun multitacBinding (us, mtac) =
                 (us, multitactic (sign, rho) mtac)
             in
               contractMultitactic (composeMultitactics (List.map multitacBinding bindings))
             end
         | Stmt.TAC tac =>
             tactic (sign, rho) tac
         | Stmt.VAR x =>
             Syn.VarCtx.lookup rho x

    and tactic (sign, rho) =
      tacticR statement (sign, rho)

    and multitactic (sign, rho) mtac =
      case Multi.out sign mtac of
           Multi.ALL stmt =>
             MT.ALL o statement (sign, rho) stmt
         | Multi.EACH stmts =>
             let
               val ts = List.map (statement (sign, rho)) stmts
             in
               fn alpha =>
                 MT.EACH' (List.map (fn t => t alpha) ts)
             end
         | Multi.FOCUS (i, stmt) =>
             MT.FOCUS i o statement (sign, rho) stmt
  end
end
