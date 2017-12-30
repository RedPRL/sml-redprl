structure VarianceData = 
struct
  (* favonia: I do not like the current usage of "invariant" in many PLs,
   *          so I coined the word "anti-variant". *)
  datatype variance = COVAR | CONTRAVAR | ANTIVAR
end

signature VARIANCE = 
sig
  datatype t = datatype VarianceData.variance

  val compose : t * t -> t
  val flip : t -> t
end