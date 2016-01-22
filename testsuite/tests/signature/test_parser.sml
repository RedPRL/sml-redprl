structure TestSignatureParser =
struct
  open Sum

  val message = "signature_parser_test has failed"
  val () = OS.FileSys.chDir "testsuite/tests/signature/"
  val input = TextIO.inputAll (TextIO.openIn "signature_parser_test.jonprl")

  val parsed = CharParser.parseString SignatureParser.parseSigExp input

  open StringSignatureDecl

  val printDecl =
    fn (lbl, DEF {parameters, arguments, definiens, sort}) =>
         print ("def " ^ lbl ^ " : " ^ sort ^ " = [" ^ definiens ^ "].")
     | _ => ()

  local
    open AstSignature.Telescope
  in
    fun printSign sign =
      case ConsView.out sign of
          ConsView.Cons (l, d, sign') =>
            (printDecl (l, d); printSign sign')
        | ConsView.Empty => ()
  end


  val () =
    case parsed of
        INL s => raise Fail (message ^ ": " ^ s)
      | INR t => printSign t
end
