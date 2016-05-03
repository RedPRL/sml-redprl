structure LvlParser :
sig
  val parseLevel
    : (Sort.t -> Ast.ast CharParser.charParser)
    -> Ast.ast ParserCombinators.fixityitem CharParser.charParser
end =
struct
  open CharParser ParserCombinators RedTokenParser
  open Ast OperatorData LevelOperatorData SortData
  infix $ \ $#

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  fun parseLevel f =
    let
      val parseBase =
        symbol "lbase"
          wth (fn u =>
            LVL_OP LBASE $ [])
      val parseSucc =
        symbol "lsuc" >> parens (f LVL)
          wth (fn l =>
            LVL_OP LSUCC $ [([],[]) \ l])
    in
      (try parseSucc
        || parseBase) wth Atm
    end
end
