structure Selector :> SELECTOR = 
struct
  datatype 'a t = IN_CONCL | IN_HYP of 'a

  val variance =
    fn IN_CONCL => Variance.COVAR
     | IN_HYP _ => Variance.CONTRAVAR
end