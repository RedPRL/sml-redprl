structure MlType :> ML_TYPE =
struct
  datatype vty = datatype MlTypeData.vty
  datatype cty = datatype MlTypeData.cty

  val rec eqVty =
    fn (ONE, ONE) => true
     | (ONE, _) => false
     | (DOWN c0, DOWN c1) => eqCty (c0, c1)
     | (DOWN _, _) => false
     | (TERM s0, TERM s1) => s0 = s1
     | (TERM _, _) => false
     | (THM s0, THM s1) => s0 = s1
     | (THM _, _) => false
     | (ABS (vls0, v0), ABS (vls1, v1)) => vls0 = vls1 andalso eqVty (v0, v1)
     | (ABS _, _) => false
     | (METAS vls0, METAS vls1) => vls0 = vls1
     | (METAS _, _) => false
     | (DATA_INFO vls0, DATA_INFO vls1) => InductiveSpec.eqPrecomputedValences (vls0, vls1)
     | (DATA_INFO _, _) => false

  and eqCty =
    fn (UP v0, UP v1) => eqVty (v0, v1)
     | (UP _, _) => false
     | (FUN (v0, c0), FUN (v1, c1)) => eqVty (v0, v1) andalso eqCty (c0, c1)
     | (FUN _, _) => false
end
