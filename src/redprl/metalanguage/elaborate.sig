signature ML_ELABORATE = 
sig
  type env
  type ivalue
  type icmd
  type evalue
  type ecmd
  type vty
  type cty

  val elabValue : evalue -> env -> ivalue * vty
  val elabCmd : ecmd -> env -> icmd * cty
end
