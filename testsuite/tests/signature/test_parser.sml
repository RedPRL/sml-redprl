structure TestSignatureParser =
struct
  open Sum

  val message = "signature_parser_test has failed"
  val input = TextIO.inputAll (TextIO.openIn "testsuite/tests/signature/signature_parser_test.jonprl")

  val parsed = CharParser.parseString SignatureParser.parseSigExp input

  open AstSignatureDecl

  val paramsToString =
    ListSpine.pretty
      (fn (u, tau) => Symbol.toString u ^ " : " ^ Sort.toString tau)
      ","

  val argsToString =
    ListSpine.pretty
      (fn (m, vl) => Metavariable.toString m ^ " : " ^ Valence.toString vl)
      ";"

  fun printDecl (lbl, {parameters, arguments, definiens, sort}) =
    print
      ("Def "
         ^ Symbol.toString lbl
         ^ "[" ^ paramsToString parameters ^ "]"
         ^ "(" ^ argsToString arguments ^ ")"
         ^ " : " ^ Sort.toString sort
         ^ " = ["
         ^ ShowAbt.toString definiens
         ^ "].\n")

  local
    open AbtSignature.Telescope
  in
    fun printSign sign =
      case ConsView.out sign of
          ConsView.Cons (l, d, sign') =>
            (printDecl (l, AbtSignature.undef d); printSign sign')
        | ConsView.Empty => ()
  end


  val () =
    case parsed of
        INL s => raise Fail (message ^ ": " ^ s)
      | INR sign =>
          let
            val elab = ValidationElab.transport o BindSignatureElab.transport
            val sign' = elab sign
            val _ = printSign sign'
          in
            ()
          end
end
