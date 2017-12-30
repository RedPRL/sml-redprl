signature SELECTOR = 
sig
  datatype 'a t = IN_CONCL | IN_HYP of 'a
  val variance : 'a t -> Variance.t
end
