(* Grammar Specification:
 * https://github.com/RedPrl/sml-redprl/blob/master/doc/definition.pdf *)

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
          (fn ((x, vl : RedPrlAtomicValence.t), d) => Dict.insert d x (Metavariable.named x, vl))
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


  structure Syn = RedPrlAstSyntax and Ast = RedPrlAst

  local
    open SortData
  in
    val defaultTac =
      Syn.into Syn.TAC_ID

    val recordTop =
      Syn.into (Syn.TOP EXP)

    fun recordTyCons (lbl, a) b =
      Syn.into (Syn.RECORD_TY (lbl, a, lbl, b))
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
          val parseDefaultTac = !! spaces wth (fn (_, pos) => RedPrlAst.annotate pos defaultTac)
          val parseDefiniens = TermParser.parseTerm sign rho SortData.TAC || parseDefaultTac
        in
          squares parseDefiniens wth (fn term =>
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
    in
      (parseOpid' && parseParams' && parseArgs') -- (fn (opid, (params, args)) =>
        let
          val rho = makeNameStore args
          val parseGoal = colon >> squares (TermParser.parseTerm sign rho SortData.EXP) && parseSort'
          val parseDefaultTac = !! spaces wth (fn (_, pos) => Ast.annotate pos defaultTac)
          val parseScript = reserved "by" >> squares (TermParser.parseTerm sign rho SortData.TAC || parseDefaultTac)
        in
          parseGoal && parseScript wth (fn ((goal, tau), script) =>
            (opid,
             {parameters = params,
              arguments = List.map (fn (m, v) => rho m) args,
              sort = SortData.THM tau,
              definiens = Ast.setAnnotation (Ast.getAnnotation script) (Syn.into (Syn.REFINE_SCRIPT (tau, goal, script, Syn.into (Syn.OPT_NONE tau))))}))
        end) ?? "theorem"
    end

  fun parseSigDecl sign : (opid * decl) charParser =
    (parseDefinition sign || parseTactic sign || parseTheorem sign) -- (fn (opid, d) =>
      succeed (opid, AstSignature.def d)
        handle e => fail (exnMessage e))
    ?? "sigdecl"

  fun parseSymDecl sign : (symbol * decl) charParser =
    reserved "Sym" >> parseSymBind sign wth (fn (u, tau) =>
        (u, AstSignature.symDecl tau))
    ?? "symdecl"

  fun parseRcdDecl sign : AstSignature.sign charParser =
    let
      val parseOpid' = reserved "Record" >> parseOpid
      val parseParams' = squares (parseParams sign) || succeed []
      val parseArgs' = parens (parseArgs sign) || succeed []
    in
      !! ((parseOpid' && parseParams' && parseArgs' << symbol "=") -- (fn (opid, (params, args)) =>
        let
          val rho = makeNameStore args
          val parseTerm' = TermParser.parseTerm sign rho SortData.EXP
          val parseRow = parseSymid << colon && parseTerm'
          val parseRows = braces (commaSep parseRow)
        in
          braces (commaSep parseRow) wth (fn rows => (rho, opid, params, args, rows))
        end))
      wth (fn ((rho, opid, params, args, rows), pos : Pos.t) =>
          let
            val sign' = List.foldr (fn ((lbl, a), sign') => AstSignature.Telescope.snoc sign' lbl (AstSignature.symDecl SortData.RCD_LBL, SOME pos)) sign rows
            val definiens = List.foldr (fn ((lbl, a), b) => recordTyCons (lbl, a) b) recordTop rows
            val def =
             {parameters = params,
              arguments = List.map (fn (m, v) => rho m) args,
              sort = SortData.EXP,
              definiens = definiens}
          in
            AstSignature.Telescope.snoc sign' opid (AstSignature.def def, SOME pos)
          end)
    end

  fun parseSigExtension sign : AstSignature.sign charParser =
    parseRcdDecl sign
      || (!! (parseSigDecl sign || parseSymDecl sign)) wth (fn ((u, dcl), pos) => AstSignature.Telescope.snoc sign u (dcl, SOME pos))

  fun parseSigExp' sign =
    opt (whiteSpace >> parseSigExtension sign << dot) -- (fn osign =>
      case osign of
           NONE => succeed sign << whiteSpace << eos
         | SOME sign' => parseSigExp' sign')

  val parseSigExp = parseSigExp' AstSignature.Telescope.empty ?? "sig"
end

structure SignatureParser = SignatureParser (TermParser)
