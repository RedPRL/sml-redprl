signature TERM_PARSER =
sig
  type metavariable_table = string -> Ast.metavariable * Valence.t
  val parseTerm
    : AstSignature.sign
    -> metavariable_table
    -> Sort.t
    -> Ast.ast CharParser.charParser
end

