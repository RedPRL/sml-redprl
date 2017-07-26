functor NominalLcfTactical (S : NOMINAL_LCF_STRUCTURE) = 
struct
  local
    open S
  in

    type 'a tactic = 'a Spr.point -> Lcf.jdg Lcf.tactic
    type 'a multitactic = 'a Spr.point -> Lcf.jdg Lcf.multitactic

    fun tacToMultitac (t : 'a tactic) : 'a multitactic = 
      Lcf.all o t 

    fun multitacToTac (mt : 'a multitactic) : 'a tactic =
      fn alpha => 
        Lcf.mul Lcf.isjdg o mt alpha o Lcf.idn

    fun seq (mt1 : 'a multitactic, us : 'a Spr.neigh, mt2 : 'a multitactic) : 'a multitactic = fn alpha => fn st =>
      let
        val beta = Spr.prepend us alpha
        val (beta', modulus) = Spr.probe (Spr.prepend us beta)
        val st' = mt1 beta' st
        val l = Int.max (0, !modulus - List.length us)
      in
        mt2 (Spr.bite l alpha) (Lcf.mul Lcf.isjdg st')
      end

    fun then_ (t1 : 'a tactic, t2 : 'a tactic) : 'a tactic = 
      multitacToTac (seq (tacToMultitac t1, [], tacToMultitac t2))

    fun thenl (t : 'a tactic, ts : 'a tactic list) : 'a tactic = 
      multitacToTac (seq (tacToMultitac t, [], fn alpha => Lcf.eachSeq (List.map (fn t => t alpha) ts)))

    fun thenl' (t : 'a tactic, us : 'a Spr.neigh, ts : 'a tactic list) = 
      multitacToTac (seq (tacToMultitac t, us, fn alpha => Lcf.eachSeq (List.map (fn t => t alpha) ts)))

    fun orelse_ (t1 : 'a tactic, t2 : 'a tactic) : 'a tactic = 
      fn alpha => 
        Lcf.orelse_ (t1 alpha, t2 alpha)
  end
end