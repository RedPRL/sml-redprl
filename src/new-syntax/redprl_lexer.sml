structure RedPrlLrVals =
  RedPrlLrValsFun(structure Token = LrParser.Token)

structure RedPrlLex =
  RedPrlLexFun(structure Tokens = RedPrlLrVals.Tokens)
