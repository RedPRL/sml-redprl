structure Variance :> VARIANCE = 
struct
  datatype variance = datatype VarianceData.variance
  val compose =
    fn (ANTIVAR, _) => ANTIVAR
     | (_, ANTIVAR) => ANTIVAR
     | (COVAR, COVAR) => COVAR
     | (CONTRAVAR, CONTRAVAR) => COVAR
     | (COVAR, CONTRAVAR) => CONTRAVAR
     | (COTRAVAR, COVAR) => CONTRAVAR

  (* variants *)
  val flip =
    fn COVAR => CONTRAVAR
     | CONTRAVAR => COVAR
     | ANTIVAR => ANTIVAR     
end