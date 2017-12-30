structure VarianceData = 
struct
  (* favonia: I do not like the current usage of "invariant" in many PLs,
   *          so I coined the word "anti-variant". *)
  datatype variance = COVAR | CONTRAVAR | ANTIVAR
end

signature VARIANCE = 
sig
  datatype variance = datatype VarianceData.variance

  val compose : variance * variance -> variance
  val flip : variance -> variance
end