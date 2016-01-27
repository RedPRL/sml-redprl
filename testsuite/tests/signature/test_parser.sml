structure TestSignatureParser =
struct
  open Sum

  val message = "signature_parser_test has failed"
  val input = TextIO.inputAll (TextIO.openIn "testsuite/tests/signature/signature_parser_test.jonprl")

  val parsed = CharParser.parseString SignatureParser.parseSigExp input

  open AstSignatureDecl


  val paramsToString =
    ListSpine.pretty
      (fn (u, tau) => u ^ " : " ^ Sort.Show.toString tau)
      ","

  val argsToString =
    ListSpine.pretty
      (fn (m, vl) => Metavariable.Show.toString m ^ " : " ^ Valence.Show.toString vl)
      ";"

  fun printDecl (lbl, DEF {parameters, arguments, definiens, sort}) =
    print
      ("Def "
         ^ lbl
         ^ "[" ^ paramsToString parameters ^ "]"
         ^ "(" ^ argsToString arguments ^ ")"
         ^ " : " ^ Sort.Show.toString sort
         ^ " = ["
         ^ Ast.Show.toString definiens
         ^ "].\n")

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
      | INR sign =>
          let
            val _ = printSign sign
            val elab = ValidationElab.transport o BindSignatureElab.transport
            val _ = elab sign
          in
            ()
          end
end
