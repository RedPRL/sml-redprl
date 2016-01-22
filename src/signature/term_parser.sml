structure TermParser : TERM_PARSER =
struct
  type metavariable_table = string -> Ast.metavariable

  open ParserCombinators CharParser
  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure LangDef :> LANGUAGE_DEF =
  struct
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
    val reservedOpNames = ["="]
    val caseSensitive = true
  end

  structure TokenParser = TokenParser (LangDef)
  open TokenParser

  local
    open SortData
  in
    fun parseSort _ =
      symbol "exp" return EXP
      || symbol "lvl" return LVL
      || symbol "tac" return TAC
  end

  local
    open Ast OperatorData ScriptOperatorData
    infix $ \
  in
    (* TODO *)
    fun parseTerm _ rho =
      symbol "todo" return (` "todo")

    (* TODO *)
    fun parseTactic _ rho =
      symbol "id" return (S ID $ [])
  end
end

