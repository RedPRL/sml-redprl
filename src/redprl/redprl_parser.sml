structure RedPrlParser =
  JoinWithArg
    (structure LrParser = LrParser
     structure ParserData = RedPrlLrVals.ParserData
     structure Lex = RedPrlLex)
