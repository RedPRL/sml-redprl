functor RedPrlTactical (Lcf : LCF_TACTIC ) :
sig
  type multitactic = Lcf.jdg Lcf.multitactic
  type tactic = Lcf.jdg Lcf.tactic

  val all : tactic -> multitactic
  val each : tactic list -> multitactic
  val only : int * tactic -> multitactic
  val mprogress: multitactic -> multitactic
  val progress : tactic -> tactic
  val mrec : (multitactic -> multitactic) -> multitactic
  val trec : (tactic -> tactic) -> tactic
  val multitacToTac : multitactic -> tactic
  val seq : multitactic * multitactic -> multitactic
  val then_ : tactic * tactic -> tactic
  val thenl : tactic * tactic list -> tactic
  val orelse_ : tactic * tactic -> tactic
  val par : tactic * tactic -> tactic
  val morelse : multitactic * multitactic -> multitactic
  val mrepeat : multitactic -> multitactic
  val repeat : tactic -> tactic
  val try : tactic -> tactic
  val idn : tactic
end = 
struct
  open Lcf

  type multitactic = Lcf.jdg Lcf.multitactic
  type tactic = Lcf.jdg Lcf.tactic

  fun mrec (f : multitactic -> multitactic) : multitactic =
    fn st =>
      f (mrec f) st

  fun trec (f : tactic -> tactic) : tactic =
    fn jdg => 
      f (trec f) jdg
      

  fun multitacToTac (mt : multitactic) : tactic =
    fn jdg => 
      Lcf.M.map (Lcf.mul Lcf.isjdg) (Lcf.M.mul (Lcf.M.map mt (Lcf.idn jdg)))


  fun seq (mt1 : multitactic, mt2 : multitactic) : multitactic = fn st =>
    let
      val st' = mt1 st
    in
      Lcf.M.mul (Lcf.M.map (mt2 o Lcf.mul Lcf.isjdg) st')
    end

  val all = allSeq
  val each = eachSeq

  fun then_ (t1 : tactic, t2 : tactic) : tactic = 
    multitacToTac (seq (allSeq t1, allSeq t2))

  fun thenl (t : tactic, ts : tactic list) : tactic = 
    multitacToTac (seq (allSeq t, eachSeq ts))

  fun mtry (mt : multitactic) : multitactic = 
    morelse (mt, all idn)

  fun try (t : tactic) : tactic = 
    orelse_ (t, idn)

  fun mrepeat (mt : multitactic) : multitactic = 
    mrec (fn mt' => mtry (seq (mprogress mt, mt')))

  fun repeat (t : tactic) : tactic = 
    trec (fn t' => try (then_ (progress t, t')))

  fun try (t : tactic) : tactic = 
    orelse_ (t, idn)
end
