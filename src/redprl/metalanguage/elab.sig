signature ML_ELAB = 
sig
  structure I : ML_DATA

  datatype eterm = datatype SyntaxData.E.term

  type env

  val elabCterm : env -> eterm * I.ctype -> I.cterm
  val elabVterm : env -> eterm * I.vtype -> I.vterm
end