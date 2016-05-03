structure GenericParser :
sig
  type metavariable_table = string -> Ast.metavariable * Valence.t
  val parseGeneric
    : AstSignature.sign
    -> metavariable_table
    -> (Sort.t -> Ast.ast CharParser.charParser)
    -> Sort.t
    -> Ast.ast CharParser.charParser
end =
struct
  type metavariable_table = string -> Ast.metavariable * Valence.t

  open CharParser ParserCombinators RedTokenParser
  open AstSignature AstSignatureDecl Ast OperatorData NominalLcfOperatorData CttOperatorData AtomsOperatorData SortData RecordOperatorData
  infix $ \ $#

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  val parseSymbol = identifier
  val parseVariable = identifier

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

  fun parseGeneric sign rho f tau =
    let
      fun parseParameters n =
        squares (separateN n parseSymbol comma)
          || (if n = 0 then succeed [] else fail "")

      val parseCustomOperator =
        identifier -- (fn opid =>
          case Telescope.find sign opid of
               NONE => fail "opid not in signature"
             | SOME (SYMDCL _) => fail "opid not in signature"
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
        || parens (f tau)
    end
end
