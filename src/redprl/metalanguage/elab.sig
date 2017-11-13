signature ML_ELAB = 
sig
  structure I : ML_DATA

  datatype eterm = datatype SyntaxData.E.term

  type name_env = I.var StringListDict.dict

  val elabCterm : name_env -> eterm * I.ctype -> I.cterm
end