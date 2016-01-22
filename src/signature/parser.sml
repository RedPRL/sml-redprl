(* The grammar can be found at
   https://github.com/JonPRL/sml-red-jonprl/blob/master/doc/signatures.pdf *)

structure SignatureParser =
struct

  open ParserCombinators
  open CharParser

  open StringSignature

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  fun inBrackets p = char #"[" >> p << char #"]"
  fun inParentheses p = char #"(" >> p << char #")"
  fun inBraces p = char #"{" >> p << char #"}"

  val skipChars = repeatSkip (space <|> char #"\t" <|> char #"\n")

  val opid = repeat1 letter wth String.implode
  val sortid = repeat1 letter wth String.implode
  val term = skipChars >> (repeat letter wth String.implode) << skipChars
  val metaid = repeat1 letter wth String.implode
  val symid = repeat1 letter wth String.implode

  val sortlist = separate sortid (char #"," >> space)

  val valence = opt (opt (inBraces sortlist) &&
    opt (inBrackets sortlist) << char #".") && sortid wth
      (fn (SOME (SOME s1, SOME s2), s3) => (s1, s2, s3)
        | (SOME (SOME s1, NONE), s2) => (s1, [], s2)
        | (SOME (NONE, SOME s1), s2) => ([], s1, s2)
        | (SOME (NONE, NONE), s) => ([], [], s)
        | (NONE, s) => ([], [], s))

  val metabind = metaid && (space >> char #":" >> space >> valence) wth
    (fn (m, v) => (m, v))

  val symbind = symid && (space >> char #":" >> space >> sortid)

  val args = separate metabind (char #"," >> space)
  val params = separate symbind (char #"," >> space)

  val definition : (opid * def) charParser =
    (string "Def" >> space >> opid) && opt (inBrackets params) &&
    opt (inParentheses args) && (space >> char #":" >> space >> sortid) &&
    (space >> char #"=" >> space >> inBrackets term) wth
      (fn (opid, (SOME p, (SOME a, (s, t)))) =>
            (opid, { parameters=p, arguments=a, sort=s, definiens=t })
        | (opid, (NONE, (SOME a, (s, t)))) =>
            (opid, { parameters=[], arguments=a, sort=s, definiens=t })
        | (opid, (SOME p, (NONE, (s, t)))) =>
            (opid, { parameters=p, arguments=[], sort=s, definiens=t })
        | (opid, (NONE, (NONE, (s, t)))) =>
            (opid, { parameters=[], arguments=[], sort=s, definiens=t }))

  val tactic : (opid * tac) charParser = (string "Tac" >> space >> opid) &&
    opt (inBrackets params) && opt (inParentheses args) &&
    (space >> char #"=" >> space >> inBrackets term) wth
      (fn (opid, (SOME p, (SOME a, t))) =>
            (opid, { parameters=p, arguments=a, script=t })
        | (opid, (NONE, (SOME a, t))) =>
            (opid, { parameters=[], arguments=a, script=t })
        | (opid, (SOME p, (NONE, t))) =>
            (opid, { parameters=p, arguments=[], script=t })
        | (opid, (NONE, (NONE, t))) =>
            (opid, { parameters=[], arguments=[], script=t }))

  val theorem : (opid * thm) charParser = (string "Thm" >> space >> opid) &&
    opt (inBrackets params) && opt (inParentheses args) &&
    (space >> char #":" >> space >> inBrackets term) &&
    (space >> string "by" >> space >> inBrackets term) wth
      (fn (opid, (SOME p, (SOME a, (t1, t2)))) =>
            (opid, { parameters=p, arguments=a, goal=t1, script=t2 })
        | (opid, (NONE, (SOME a, (t1, t2)))) =>
            (opid, { parameters=[], arguments=a, goal=t1, script=t2 })
        | (opid, (SOME p, (NONE, (t1, t2)))) =>
            (opid, { parameters=p, arguments=[], goal=t1, script=t2 })
        | (opid, (NONE, (NONE, (t1, t2)))) =>
            (opid, { parameters=[], arguments=[], goal=t1, script=t2 }))

  val sigdec : (opid * decl) charParser =
    (definition << skipChars) wth
      (fn (opid, d) => (opid, StringSignatureDecl.DEF d)) ||
    (tactic << skipChars) wth
      (fn (opid, t) => (opid, StringSignatureDecl.TAC t)) ||
    (theorem << skipChars) wth
      (fn (opid, t) => (opid, StringSignatureDecl.THM t))

  val sigexp : sign charParser =
    (sepEnd sigdec (char #".") wth
      (fn (declarations) =>
        (foldl (fn ((l, d), b) =>
          Telescope.cons (l, d) b) Telescope.empty declarations)))
    << skipChars << not any

end
