signature ML_ELABORATE = 
sig
  type env
  type ivalue
  type icmd
  type evalue
  type ecmd
  type vty
  type cty

  val elabValue : env -> evalue -> ivalue * vty
  val elabCmd : env -> ecmd -> icmd * cty
end
