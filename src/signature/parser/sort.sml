structure SortParser :
sig
  val parseSort
    : AstSignature.sign
    -> Sort.t CharParser.charParser
end =
struct
  open CharParser ParserCombinators RedTokenParser SortData
  infix $ \ $#

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  fun parseSort _ =
    ParserCombinators.fix (fn p =>
      symbol "exp" return EXP
      || symbol "lvl" return LVL
      || symbol "tac" return TAC
      || symbol "thm" >> braces p wth THM
      || symbol "mtac" return MTAC
      || symbol "vec" >> braces p wth VEC
      || symbol "str" return STR
      || symbol "lbl" return RCD_LBL)
end
