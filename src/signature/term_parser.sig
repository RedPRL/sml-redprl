signature TERM_PARSER =
sig
  type metavariable_table = string -> Ast.metavariable
  val parseSort : AstSignature.sign -> Sort.t CharParser.charParser
  val parseTerm : AstSignature.sign -> metavariable_table -> Sort.t -> Ast.ast CharParser.charParser
end

