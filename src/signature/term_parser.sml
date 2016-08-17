structure TermParser : TERM_PARSER =
struct
  structure Ast = RedPrlAst
  type metavariable_table = string -> Ast.metavariable * RedPrlAtomicValence.t

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

  type 'a parser_family = RedPrlAtomicSort.t -> 'a charParser
  type 'a endo = 'a -> 'a

  (* to fix a recursive family of parsers *)
  fun fix' (f : 'a parser_family endo) : 'a parser_family =
    fn tau =>
      force (fn () => f (fix' f) tau)


  local
    open AstSignature AstSignatureDecl SortData
    structure Syn = RedPrlAstSyntax
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
              Syn.into (Syn.EXTRACT_WITNESS (tau, m))))

    fun parseTerm' sign rho f tau =
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
             wth (fn xs => Syn.into (Syn.VEC_LITERAL (tau, xs)))
             wth Atm
         | STR =>
           stringLiteral
             wth (Syn.into o Syn.STR_LITERAL)
             wth Atm
         | MTAC => liftParser @@ TacParser.parseMultitac sign rho f
         | TAC => liftParser @@ TacParser.parseTac sign rho f
         | _ => liftParser (fail "Not implemented")
      end

    fun parseTerm sign rho sigma =
      let
        val parser =
          fix' (fn f => fn tau =>
            let
              val p = parseTerm' sign rho f tau
            in
              spaces >> parsefixityadj p Left (Syn.into o Syn.AP) << spaces
            end)
      in
        !! (parser sigma) wth (fn (m, pos) => Ast.annotate pos m)
      end
  end
end
