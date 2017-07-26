signature NOMINAL_LCF_STRUCTURE = 
sig
  (* A model begins with a tactic metalanguage. *)
  structure Lcf : LCF_UTIL

  (* The nominal character of the semantics is dealt with using a Brouwerian
   * spread, a space whose points are free choice sequences. A free choice
   * sequence is a stream of constructible objects which are chosen not by a
   * computable function, but by interaction with a subject (i.e. a user). *)
  structure Spr : SPREAD


  (* A "nominal" object is a functional which _continuously_ transforms a free
   * choice sequence into a result. *)
  type 'a nominal = Sym.t Spr.point -> 'a

  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal
end

functor NominalLcfTactical (S : NOMINAL_LCF_STRUCTURE) = 
struct
  local
    open S
  in

    fun idn alpha =
      Lcf.idn

    fun all (t : tactic) : multitactic = 
      Lcf.allSeq o t 
    
    (* TODO: consider a version where 'alpha' is not shared among the branches. That may be better-behaved. *)
    fun each (ts : tactic list) : multitactic = 
      fn alpha => 
        Lcf.eachSeq (List.map (fn t => t alpha) ts)

    fun only (i, t) : multitactic = 
      fn alpha => 
        Lcf.only (i, t alpha)

    fun mprogress (mt : multitactic) : multitactic = 
      fn alpha => 
        Lcf.mprogress (mt alpha)

    fun mrec (f : multitactic -> multitactic) : multitactic =
      fn alpha => 
        f (mrec f) alpha

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
      multitacToTac (seq (all t1, [], all t2))

    fun thenl (t : tactic, ts : tactic list) : tactic = 
      multitacToTac (seq (all t, [], each ts))

    fun thenl' (t : tactic, us : Sym.t list, ts : tactic list) = 
      multitacToTac (seq (all t, us, each ts))

    fun morelse (mt1 : multitactic, mt2 : multitactic) : multitactic = 
      fn alpha => 
        Lcf.morelse (mt1 alpha, mt2 alpha)

    fun orelse_ (t1 : tactic, t2 : tactic) : tactic = 
      fn alpha =>
        Lcf.orelse_ (t1 alpha, t2 alpha)

    fun mtry (mt : multitactic) : multitactic = 
      morelse (mt, all idn)

    fun mrepeat (mt : multitactic) : multitactic = 
      mrec (fn mt' => mtry (seq (mprogress mt, [], mt')))

    fun try (t : tactic) : tactic = 
      orelse_ (t, idn)

  end
end