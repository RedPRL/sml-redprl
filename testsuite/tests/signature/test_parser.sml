structure TestSignatureParser =
struct
  open Sum

  val message = "signature_parser_test has failed"
  val () = OS.FileSys.chDir "testsuite/tests/signature/"
  val input = TextIO.inputAll (TextIO.openIn "signature_parser_test.jonprl")

  val parsed = CharParser.parseString SignatureParser.sigexp input
  val () =
    (case parsed of
      (INL s) => raise Fail (message ^ ": " ^ s)
    | (INR t) =>
      AstSignature.Telescope.foldl (fn (StringSignatureDecl.DEF { parameters=p, arguments=a, definiens=d, sort=s }, _) =>
        (print d; print s)) () t)
end
