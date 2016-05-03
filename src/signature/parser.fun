(* Grammar Specification:
 * https://github.com/RedPRL/sml-redprl/blob/master/doc/definition.pdf *)

functor SignatureParser (TermParser : TERM_PARSER) =
struct

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
    val opStart = fail "no reserved ops" : scanner
    val opLetter = opStart
    val reservedNames = ["Def", "Thm", "Tac", "Sym", "Record", "by"]
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TokenParser = TokenParser (LangDef)
  open TokenParser AstSignature

  val parseOpid = identifier ?? "opid"
  val parseMetaid = identifier ?? "metaid"
  val parseSymid = identifier ?? "symid"

  fun parseSort sign = SortParser.parseSort sign ?? "sort"
  fun parseSortList sign = commaSep (parseSort sign) ?? "sortlist"

  fun parseValence sign =
    let
      val parseSymSorts = braces (parseSortList sign)
      val parseVarSorts = squares (parseSortList sign)
    in
      opt ((opt parseSymSorts && opt parseVarSorts) << dot) && parseSort sign wth
        (fn (SOME (SOME s1, SOME s2), s3) => ((s1, s2), s3)
          | (SOME (SOME s1, NONE), s2) => ((s1, []), s2)
          | (SOME (NONE, SOME s1), s2) => (([], s1), s2)
          | (SOME (NONE, NONE), s) => (([], []), s)
          | (NONE, s) => (([], []), s))
      ?? "valence"
    end

  fun parseMetaBind sign =
    (parseMetaid << colon)
      && parseValence sign

  fun parseSymBind sign =
    (parseSymid << colon)
      && parseSort sign

  fun parseArgs sign =
    commaSep (parseMetaBind sign)
      ?? "args"

  fun parseParams sign =
    commaSep (parseSymBind sign)
      ?? "params"

  local
    structure Dict = SplayDict (structure Key = StringOrdered)
  in
    val makeNameStore =
      Dict.lookup o
        List.foldl
          (fn ((x, vl : Valence.t), d) => Dict.insert d x (Metavariable.named x, vl))
          Dict.empty
  end

  fun parseDefinition sign : (opid * def) charParser =
    let
      val parseOpid' = reserved "Def" >> parseOpid
      val parseParams' = squares (parseParams sign) || succeed []
      val parseArgs' = parens (parseArgs sign) || succeed []
      val parseSort' = colon >> parseSort sign << symbol "="
    in
      (parseOpid' && parseParams' && parseArgs' && parseSort') -- (fn (opid, (params, (args, sort))) =>
        let
          val rho = makeNameStore args
        in
          squares (TermParser.parseTerm sign rho sort) wth (fn term =>
            (opid,
             {parameters = params,
              arguments = List.map (fn (m, v) => rho m) args,
              sort = sort,
              definiens = term}))
        end) ?? "definition"
    end

  fun parseTactic sign : (opid * def) charParser =
    let
      val parseOpid' = reserved "Tac" >> parseOpid
      val parseParams' = squares (parseParams sign) || succeed []
      val parseArgs' = parens (parseArgs sign) || succeed []
    in
      (parseOpid' && parseParams' && parseArgs' << symbol "=") -- (fn (opid, (params, args)) =>
        let
          val rho = makeNameStore args
        in
          squares (TermParser.parseTerm sign rho SortData.TAC) wth (fn term =>
            (opid,
             {parameters = params,
              arguments = List.map (fn (m, v) => rho m) args,
              sort = SortData.TAC,
              definiens = term}))
        end) ?? "tactic"
    end

  fun parseTheorem sign : (opid * def) charParser =
    let
      val parseOpid' = reserved "Thm" >> parseOpid
      val parseParams' = squares (parseParams sign) || succeed []
      val parseArgs' = parens (parseArgs sign) || succeed []
      val parseSort' = (colon >> parseSort sign) || succeed SortData.EXP
      open Ast
      infix $ \
    in
      (parseOpid' && parseParams' && parseArgs') -- (fn (opid, (params, args)) =>
        let
          val rho = makeNameStore args
          val parseGoal = colon >> squares (TermParser.parseTerm sign rho SortData.EXP) && parseSort'
          val parseScript = reserved "by" >> squares (TermParser.parseTerm sign rho SortData.TAC)
        in
          parseGoal && parseScript wth (fn ((goal, tau), script) =>
            (opid,
             {parameters = params,
              arguments = List.map (fn (m, v) => rho m) args,
              sort = SortData.THM tau,
              definiens =
                OperatorData.REFINE tau$
                  [([],[]) \ goal,
                   ([],[]) \ script,
                   ([],[]) \ (OperatorData.OP_NONE tau $ [])]}))
        end) ?? "theorem"
    end

  fun parseSigDecl sign : (opid * decl) charParser =
    (parseDefinition sign || parseTactic sign || parseTheorem sign) -- (fn (opid, d) =>
      succeed (opid, AstSignature.def d)
        handle e => fail (exnMessage e))
    ?? "sigdecl"

  fun parseSymDecl sign : (symbol * decl) charParser =
    reserved "Sym" >> parseSymBind sign wth (fn (u, tau) =>
        (u, AstSignature.symdcl tau))
    ?? "symdecl"

  fun parseSigExp' sign =
    opt (whiteSpace >> (parseSigDecl sign || parseSymDecl sign) << dot) -- (fn odecl =>
      case odecl of
           NONE => succeed sign << whiteSpace << eos
         | SOME (x,decl) => parseSigExp' (AstSignature.Telescope.snoc sign x decl))

  val parseSigExp = parseSigExp' AstSignature.Telescope.empty ?? "sig"
end

structure SignatureParser = SignatureParser (TermParser)
