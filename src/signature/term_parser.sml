structure TermParser : TERM_PARSER =
struct
  type metavariable_table = string -> Ast.metavariable * Valence.t

  open ParserCombinators CharParser
  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  open RedTokenParser

  local
    open SortData
  in
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

  val force =
    ParserCombinators.$

  type 'a parser_family = Sort.t -> 'a charParser
  type 'a endo = 'a -> 'a

  (* to fix a recursive family of parsers *)
  fun fix' (f : 'a parser_family endo) : 'a parser_family =
    fn tau =>
      force (fn () => f (fix' f) tau)


  local
    open AstSignature AstSignatureDecl Ast OperatorData NominalLcfOperatorData CttOperatorData LevelOperatorData AtomsOperatorData SortData RecordOperatorData
    infix $ \ $#
  in
    val parseSymbol = identifier
    val parseVariable = identifier

    fun @@ (f, x) = f x
    infixr @@

    fun parseExtract sign f tau =
      symbol "extract"
        >> (braces (SortParser.parseSort sign) || succeed tau)
        -- (fn tau' =>
          parens (f (THM tau))
            wth (fn m =>
              EXTRACT tau' $ [([],[]) \ m]))

    fun parseTerm' sign rho f tau : ast fixityitem charParser =
      let
        fun liftParser p =
          parseExtract sign f tau wth Atm
            || try p
            || GenericParser.parseGeneric sign rho f tau wth Atm
      in
        case tau of
           LVL => liftParser @@ LvlParser.parseLevel f
         | EXP => liftParser @@ ExprParser.parseExpr sign f
         | VEC tau =>
           squares (commaSep (f tau))
             wth (fn xs =>
               VEC_LIT (tau, length xs) $
                 map (fn x => ([], []) \ x) xs)
             wth Atm
         | STR =>
           stringLiteral
             wth (fn str => STR_LIT str $ [])
             wth Atm
         | MTAC => liftParser @@ TacParser.parseMultitac sign rho f
         | TAC => liftParser @@ TacParser.parseTac sign rho f
         | _ => liftParser (fail "Not implemented")
      end

    fun parseTerm sign rho =
      fix' (fn f => fn tau =>
        let
          val p = parseTerm' sign rho f tau
        in
          spaces >> parsefixityadj p Left (fn (m, n) => CTT AP $ [([],[]) \ m, ([],[]) \ n]) << spaces
        end)
  end
end

