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

  fun defToString (lbl, {parameters, arguments, definiens, sort, pos}) =
    "Def "
       ^ Symbol.toString lbl
       ^ "[" ^ paramsToString parameters ^ "]"
       ^ "(" ^ argsToString arguments ^ ")"
       ^ " : " ^ RedPrlAtomicSort.toString sort
       ^ " = ["
       ^ RedPrlAbtSyntax.toString definiens
       ^ "].\n"

  fun symToString (lbl, tau) =
    "Sym "
       ^ Symbol.toString lbl
       ^ " : "
       ^ RedPrlAtomicSort.toString tau
       ^ ".\n"
  local
    open AbtSignature
    open AbtSignature.Telescope
  in
    fun printDcl (lbl, d) =
      case d of
         Decl.SYM_DECL tau => print (symToString (lbl, tau))
       | Decl.DEF def => print (defToString (lbl, def))

    fun signToString sign =
      case ConsView.out sign of
          ConsView.CONS (l, dcl, sign') =>
            ((case dcl of
                 Decl.DEF d => defToString (l, d)
               | Decl.SYM_DECL tau => symToString (l, tau)) ^ signToString sign')
        | ConsView.EMPTY => ""

    fun dumpSignJson sign =
      let
        val json = encode sign
      in
        print (Json.toString json)
      end
  end

  fun processFile fileName =
    let
      val input = TextIO.inputAll (TextIO.openIn fileName)
      val stream = CoordinatedStream.coordinate (fn x => Stream.hd x = #"\n" handle Stream.Empty => false) (Coord.init fileName) (Stream.fromString input)
      val parsed = CharParser.parseChars SignatureParser.parseSigExp stream

      (* Error messages should be printed with all lines except their first indented by two spaces;
         this is used for editor/IDE support. *)
      fun printErr msg =
        let
          val lines = String.tokens (fn c => c = #"\n") msg
          fun printErrLine x = TextIO.output (TextIO.stdErr, x ^ "\n")
        in
          case lines of
             [] => ()
           | l::ls =>
               (printErrLine l;
                List.app (fn l => printErrLine ("  " ^ l)) ls)
        end
    in
      (case parsed of
          INL s => raise RedPrlExn.RedPrlExn (NONE, s)
        | INR sign =>
            let
              val elab = ValidationElab.transport o BindSignatureElab.transport
            in
              RefineElab.execute
                (elab sign)
                printDcl
                (printErr o RedPrlExn.toString)
            end)
        handle exn =>
          (printErr (RedPrlExn.toString exn);
           OS.Process.exit OS.Process.failure)
    end
end
