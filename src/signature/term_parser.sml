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

  datatype hole = !
  fun hole ! = raise Match

  local
    open Ast OperatorData ScriptOperatorData SortData
    infix $ \
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

    fun parseAny sign rho f =
      parseVariable wth `
      (* TODO: parse metavariable applications, custom operator applications *)

    fun parseTerm sign rho =
      fix' (fn f => fn tau =>
        parseTerm' sign rho f tau
          || parseAny sign rho f)
  end
end

