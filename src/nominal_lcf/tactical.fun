functor NominalLcfTactical (S : NOMINAL_LCF_STRUCTURE) = 
struct
  local
    open S
  in

    fun tacToMultitac (t : tactic) : multitactic = 
      Lcf.all o t 
      Lcf.allSeq o t 

    fun multitacToTac (mt : multitactic) : tactic =
      fn alpha => 
        Lcf.mul Lcf.isjdg o mt alpha o Lcf.idn

    fun seq (mt1 : multitactic, us : Sym.t list, mt2 : multitactic) : multitactic = fn alpha => fn st =>
      let
        val beta = Spr.prepend us alpha
        val (beta', modulus) = Spr.probe (Spr.prepend us beta)
        val st' = mt1 beta' st
        val l = Int.max (0, !modulus - List.length us)
      in
        mt2 (Spr.bite l alpha) (Lcf.mul Lcf.isjdg st')
      end

    fun then_ (t1 : tactic, t2 : tactic) : tactic = 
      multitacToTac (seq (tacToMultitac t1, [], tacToMultitac t2))

    fun thenl (t : tactic, ts : tactic list) : tactic = 
      multitacToTac (seq (tacToMultitac t, [], fn alpha => Lcf.eachSeq (List.map (fn t => t alpha) ts)))

    fun thenl' (t : tactic, us : Sym.t list, ts : tactic list) = 
      multitacToTac (seq (tacToMultitac t, us, fn alpha => Lcf.eachSeq (List.map (fn t => t alpha) ts)))

    fun orelse_ (t1 : tactic, t2 : tactic) : tactic = 
      fn alpha =>
        Lcf.orelse_ (t1 alpha, t2 alpha)
  end
end