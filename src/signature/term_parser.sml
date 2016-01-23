structure TermParser : TERM_PARSER =
struct
  type metavariable_table = string -> Ast.metavariable * Valence.t

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
    val reservedOpNames = []
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

  val force =
    ParserCombinators.$

  type 'a parser_family = Sort.t -> 'a charParser
  type 'a endo = 'a -> 'a

  (* to fix a recursive family of parsers *)
  fun fix' (f : 'a parser_family endo) : 'a parser_family =
    fn tau =>
      force (fn () => f (fix' f) tau)

  fun tabulateSeparateN n p q =
    let
      fun go _ 0 = succeed []
        | go 0 n = p 0 && go 1 (n - 1) wth op::
        | go i n = q >> p i && go (i + 1) (n - 1) wth op::
    in
      go 0 n
    end

  fun separateN n p =
    tabulateSeparateN n (fn _ => p)


  datatype hole = !
  fun hole ! = raise Match

  local
    open AstSignature AstSignatureDecl Ast OperatorData ScriptOperatorData SortData
    infix $ \ $#
  in
    val parseSymbol = identifier
    val parseVariable = identifier

    (* TODO *)
    fun parseTerm' sign rho f =
      fn EXP =>
        fail "to be implemented"
      | TAC =>
        let
          val parseId =
            symbol "id"
              return (S ID $ [])

          val parseHyp =
            symbol "hyp"
              >> parseSymbol
              wth (fn u => S (HYP {target = u}) $ [])

          fun parseVec tau =
            commaSep (f tau)
              wth (fn xs =>
                VEC_LIT (tau, length xs) $
                  map (fn x => ([],[]) \ x) xs)

          val parseMulti =
            squares (parseVec TAC)
              wth (fn v =>
                S MULTI $ [([], []) \ v])

          val parseFocus =
            symbol "#"
              >> integer
              && braces (f TAC)
              wth (fn (i, tac) =>
                S (FOCUS {focus = i}) $
                  [([],[]) \ tac])

          val parseAtomic =
            parens (f TAC)
              || parseId
              || parseHyp
              || parseMulti
              || parseFocus

          datatype component =
              BINDING of symbol list * ast
            | ATOMIC of ast

          val parseBinding =
            commaSep parseSymbol << symbol "<-"
              && parseAtomic

          val parseComponent =
            try parseAtomic wth ATOMIC
              || parseBinding wth BINDING

          fun makeBind t1 us t2 =
            S (BIND {bindings = length us}) $
              [([],[]) \ t1, (us, []) \ t2]

          val rec componentsToScript =
            fn [] => fail "Expected tactic script"
             | [ATOMIC tac] => succeed tac
             | [BINDING _] => fail "Expected tactic after binding"
             | ATOMIC tac :: xs => componentsToScript xs wth (makeBind tac [])
             | BINDING (us, tac) :: xs => componentsToScript xs wth (makeBind tac us)
        in
          sepEnd1' parseComponent semi
            -- componentsToScript
        end
      | _ =>
        fail "to be implemented"

    fun parseAny sign rho f tau =
      let
        fun parseParameters n =
          squares (separateN n parseSymbol comma)
            || (if n = 0 then succeed [] else fail "")

        val parseCustomOperator =
          identifier -- (fn opid =>
            case Telescope.find sign opid of
                 NONE => fail "opid not in signature"
               | SOME (DEF {parameters, arguments, sort, definiens}) =>
                   parseParameters (length parameters) wth (fn us =>
                     let
                       val params = ListPair.mapEq (fn (u, (_, tau)) => (u, tau)) (us, parameters)
                       val valences = List.map (fn (_, vl) => vl) arguments
                       val arity = (valences, sort)
                     in
                       CUST (opid, params, arity)
                     end))

        fun parseSymbols n =
          braces (separateN n parseSymbol comma)
            || (if n = 0 then succeed [] else fail "")

        fun parseVariables n =
          squares (separateN n parseVariable comma)
            || (if n = 0 then succeed [] else fail "")

        val parseMetavariable =
          identifier -- (fn m =>
            succeed (rho m)
              handle _ => fail "")

        fun parseAbs ((sigmas, taus), tau) =
          let
            val m = length sigmas
            val n = length taus
            val parseDot =
              dot return ()
                || (if n + m = 0 then succeed () else fail "")
          in
            parseSymbols m
              && parseVariables n
              << parseDot && f tau
              wth (fn (us, (vs, t)) => (us, vs) \ t)
          end

        fun parseArguments valences =
          parens
            (tabulateSeparateN
              (length valences)
              (fn i => parseAbs (List.nth (valences, i)))
              semi)
            || (if length valences = 0 then succeed [] else fail "")

        val parseCustomApp =
          try parseCustomOperator -- (fn theta =>
            let
              val (valences, tau') = Operator.arity theta
            in
              if tau' = tau then
                parseArguments valences
                  wth (fn args =>
                    theta $ args)
              else
                fail "mismatched sort"
            end)

        fun parseMetaArguments sorts =
          squares
            (tabulateSeparateN
              (length sorts)
              (fn i => f (List.nth (sorts, i)))
              semi)
            || (if length sorts = 0 then succeed [] else fail "")

        val parseMetaApp =
          try parseMetavariable -- (fn (m, ((sigmas, taus), tau')) =>
            if tau = tau' then
              parseSymbols (length sigmas)
                && parseMetaArguments taus
                wth (fn (us, ts) => m $# (us, ts))
            else
              fail "mismatched sort")
      in
        parseCustomApp
          || parseMetaApp
          || parseVariable wth `
      end

    fun parseTerm sign rho =
      fix' (fn f => fn tau =>
        parseTerm' sign rho f tau
          || parseAny sign rho f tau)
  end
end

