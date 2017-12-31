functor RedPrlTactical (Lcf : LCF_TACTIC where type M.env = Sym.t NameSeq.seq) :
sig
  type multitactic = Lcf.jdg Lcf.multitactic
  type tactic = Lcf.jdg Lcf.tactic

  val all : tactic -> multitactic
  val each : tactic list -> multitactic
  val only : int * tactic -> multitactic
  val mprogress: multitactic -> multitactic
  val mrec : (multitactic -> multitactic) -> multitactic
  val multitacToTac : multitactic -> tactic
  val seq : multitactic * (Sym.t list * multitactic) -> multitactic
  val then_ : tactic * tactic -> tactic
  val thenl : tactic * tactic list -> tactic
  val thenl' : tactic * (Sym.t list * tactic list) -> tactic
  val orelse_ : tactic * tactic -> tactic
  val par : tactic * tactic -> tactic
  val morelse : multitactic * multitactic -> multitactic
  val mrepeat : multitactic -> multitactic
  val try : tactic -> tactic
  val idn : tactic
end = 
struct
  local
    structure Spr = NameSeq
  in
    type multitactic = Lcf.jdg Lcf.multitactic
    type tactic = Lcf.jdg Lcf.tactic

    val idn = Lcf.idn
    val all = Lcf.allSeq
    val each = Lcf.eachSeq
    val only = Lcf.only
    val mprogress = Lcf.mprogress

    fun mrec (f : multitactic -> multitactic) : multitactic =
      f (mrec f)


    fun multitacToTac (mt : multitactic) : tactic =
      fn jdg => 
        Lcf.M.map (Lcf.mul Lcf.isjdg) (Lcf.M.bind (Lcf.idn jdg, mt))

    fun seq (mt1 : multitactic, (us : Sym.t list, mt2 : multitactic)) : multitactic =
      fn st => 
        let
          val st' = Lcf.M.mapEnv (Spr.prepend us) (mt1 st)
        in
          Lcf.M.bind (st', mt2 o Lcf.mul Lcf.isjdg)
        end

    fun then_ (t1 : tactic, t2 : tactic) : tactic = 
      multitacToTac (seq (all t1, ([], all t2)))

    fun thenl (t : tactic, ts : tactic list) : tactic = 
      multitacToTac (seq (all t, ([], each ts)))

    fun thenl' (t : tactic, (us : Sym.t list, ts : tactic list)) = 
      multitacToTac (seq (all t, (us, each ts)))

    val morelse = Lcf.morelse
    val orelse_ = Lcf.orelse_
    val par = Lcf.par
    
    fun mtry (mt : multitactic) : multitactic = 
      morelse (mt, all idn)

    fun mrepeat (mt : multitactic) : multitactic = 
      mrec (fn mt' => mtry (seq (mprogress mt, ([], mt'))))

    fun try (t : tactic) : tactic = 
      orelse_ (t, idn)

  end
end
