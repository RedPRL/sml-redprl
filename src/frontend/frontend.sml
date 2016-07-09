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

  fun defToString (lbl, {parameters, arguments, definiens, sort}) =
    "Def "
       ^ Symbol.toString lbl
       ^ "[" ^ paramsToString parameters ^ "]"
       ^ "(" ^ argsToString arguments ^ ")"
       ^ " : " ^ RedPrlAtomicSort.toString sort
       ^ " = ["
       ^ RedPrlAbtSyntax.toString definiens
       ^ "].\n"

  fun printDef (lbl, d) =
    print (defToString (lbl, d))

  fun symToString (lbl, tau) =
    "Sym "
       ^ Symbol.toString lbl
       ^ " : "
       ^ RedPrlAtomicSort.toString tau
       ^ ".\n"

  fun printSymDcl (lbl, tau) =
    print (symToString (lbl, tau))


  local
    open AbtSignature
    open AbtSignature.Telescope
  in
    fun signToString sign =
      case ConsView.out sign of
          ConsView.CONS (l, dcl, sign') =>
            ((case dcl of
                 Decl.DEF d => defToString (l, d)
               | Decl.SYM_DECL tau => symToString (l, tau)) ^ signToString sign')
        | ConsView.EMPTY => ""

    fun printSign sign = print (signToString sign)
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
