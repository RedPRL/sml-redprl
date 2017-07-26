functor NominalLcfSemantics (M : NOMINAL_LCF_MODEL) : NOMINAL_LCF_SEMANTICS =
struct
  open M

  structure T = NominalLcfTactical (M)

  local
    open NominalLcfView
  in

    val all = 
      fn PARALLEL => Lcf.all
       | SEQUENTIAL => Lcf.allSeq

    val each = 
      fn PARALLEL => Lcf.each
       | SEQUENTIAL => Lcf.eachSeq

    fun Rec f alpha =
      f (Rec f) alpha

    (* [Σ |=[ρ] tac ==> T] *)
    fun tactic (sign, rho) tac =
      case Syn.tactic sign tac of
           RULE rl => rule (sign, rho) rl
         | MTAC mtac => T.multitacToTac (multitactic (sign, rho) mtac)

    (* [Σ |=[ρ] mtac ==> M] *)
    and multitactic (sign, rho) mtac =
      case Syn.multitactic sign mtac of
           ALL (mode, tac) =>
             all mode o tactic (sign, rho) tac
         | EACH (mode, tacs) =>
             let
               val ts = List.map (tactic (sign, rho)) tacs
             in
               fn alpha =>
                 each mode (List.map (fn t => t alpha) ts)
             end
         | FOCUS (i, tac) =>
             (fn t => Lcf.only (i, t)) o tactic (sign, rho) tac
         | REC (x, mtac) =>
             Rec (fn mt => multitactic (sign, Syn.VarCtx.insert rho x mt) mtac)
         | PROGRESS mtac' =>
             Lcf.mprogress o multitactic (sign, rho) mtac'
         | VAR x => Syn.VarCtx.lookup rho x
         | SEQ (us, mt1, mt2) =>
            T.seq (multitactic (sign, rho) mt1, us, multitactic (sign, rho) mt2)
         | ORELSE (mt1, mt2) =>
             let
               val mt1 = multitactic (sign, rho) mt1
               val mt2 = multitactic (sign, rho) mt2
             in
               fn alpha =>
                 Lcf.morelse (mt1 alpha, mt2 alpha)
             end
         | HOLE ann => 
             fn alpha => fn state => 
               let
                 val _ = M.printHole ann state
               in
                 Lcf.all Lcf.idn state
               end
  end
end
