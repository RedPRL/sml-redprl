structure RedLanguageDef :> LANGUAGE_DEF =
struct
  open ParserCombinators CharParser

  infix ||

  type scanner = char charParser
  val commentStart = SOME "(*"
  val commentEnd = SOME "*)"
  val commentLine = SOME "//"
  val nestedComments = true
  val identLetter = letter || digit
  val identStart = identLetter
  val opStart = fail "Operators not supported" : scanner
  val opLetter = opStart
  val reservedNames = ["Def", "Thm", "Tac", "by"]
  val reservedOpNames = []
  val caseSensitive = true
end

structure RedTokenParser = TokenParser (RedLanguageDef)
