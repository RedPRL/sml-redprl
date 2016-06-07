structure Frontend =
struct
  open Sum
  open AstSignatureDecl

  val paramsToString =
    ListSpine.pretty
      (fn (u, tau) => Symbol.toString u ^ " : " ^ RedPrlAtomicSort.toString tau)
      ","

  val argsToString =
    ListSpine.pretty
      (fn (m, vl) => Metavariable.toString m ^ " : " ^ RedPrlAtomicValence.toString vl)
      ";"

  fun printDef (lbl, {parameters, arguments, definiens, sort}) =
    print
      ("Def "
         ^ Symbol.toString lbl
         ^ "[" ^ paramsToString parameters ^ "]"
         ^ "(" ^ argsToString arguments ^ ")"
         ^ " : " ^ RedPrlAtomicSort.toString sort
         ^ " = ["
         ^ RedPrlAbtSyntax.toString definiens
         ^ "].\n")

  fun printSymDcl (lbl, tau) =
    print
      ("Sym "
         ^ Symbol.toString lbl
         ^ " : "
         ^ RedPrlAtomicSort.toString tau
         ^ ".\n")

  local
    open AbtSignature
    open AbtSignature.Telescope
  in
    fun printSign sign =
      case ConsView.out sign of
          ConsView.CONS (l, dcl, sign') =>
            ((case dcl of
                 Decl.DEF d => printDef (l, d)
               | Decl.SYM_DECL tau => printSymDcl (l, tau)); printSign sign')
        | ConsView.EMPTY => ()
  end

  fun processFile fileName =
    let
      val input = TextIO.inputAll (TextIO.openIn fileName)
      val parsed = CharParser.parseString SignatureParser.parseSigExp input
    in
      case parsed of
          INL s => raise Fail ("Parsing of " ^ fileName ^ " has failed: " ^ s)
        | INR sign =>
            let
              val elab = RefineElab.transport o ValidationElab.transport o BindSignatureElab.transport
              val sign' = elab sign
              val _ = printSign sign'
            in
              ()
            end
    end
end
