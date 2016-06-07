signature TERM_PARSER =
sig
  type metavariable_table = string -> AstSignature.metavariable * AstSignature.valence
  val parseTerm
    : AstSignature.sign
    -> metavariable_table
    -> AstSignature.sort
    -> AstSignature.term CharParser.charParser
end
