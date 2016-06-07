structure LvlParser :
sig
  val parseLevel
    : (AstSignature.sort -> AstSignature.term CharParser.charParser)
    -> AstSignature.term ParserCombinators.fixityitem CharParser.charParser
end =
struct
  open CharParser ParserCombinators RedTokenParser SortData

  structure Syn = RedPrlAstSyntax

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  fun parseLevel f =
    let
      val parseBase =
        symbol "lbase"
        return Syn.into Syn.LBASE

      val parseSucc =
        symbol "lsuc" >> parens (f LVL)
          wth (Syn.into o Syn.LSUCC)
    in
      (try parseSucc
        || parseBase) wth Atm
    end
end
