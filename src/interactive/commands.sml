structure Commands =
struct
  val version = "0.0.1"

  structure J = Json
  open Sum

  datatype command =
    Execute of string
  | Chunks of int

  fun getValueByKeyOrFail obj key =
    case J.getValueByKey obj key of
      SOME (J.String s) => s
    | NONE => raise Fail ("Missing attribute: " ^ key)
    | _ => raise Fail ("Wrong type of attribute:" ^ key)

  fun getIntByKeyOrFail obj key =
    case J.getValueByKey obj key of
      SOME (J.Int i) => i
    | NONE => raise Fail ("Missing attribute: " ^ key)
    | _ => raise Fail ("Wrong type of attribute:" ^ key)

  fun getCommand obj =
    case J.getValueByKey obj "cmd" of
      SOME (J.String s) =>
        (case s of
          "execute" => Execute (getValueByKeyOrFail obj "code")
        | "chunks" => Chunks (getIntByKeyOrFail obj "amount")
        | _ => raise (Fail "Unknown command"))
    | _ => raise (Fail "Command is not specified")

  fun printKeyValue k v = print ("{\"" ^ k ^ "\": \"" ^ v ^ "\"}\n")
  val printMessage = printKeyValue "msg"

  fun printInParts size list =
    let
      val num = ((List.length list) div size) + 1
      fun printPart num list =
        case (num, list) of
          (1, l) => printMessage (String.implode list)
        | (n, l) =>
          let
            val l1 = if List.length list < size
              then list else List.take (list, size)
            val l2 = if List.length list < size
              then [] else List.drop (list, size)
            in
              (
                printMessage (String.implode l1);
                print "redprl:> ";
                TextIO.inputLine TextIO.stdIn;
                printPart (n - 1) l2
              )
            end
    in
      (
        print ("{\"amount\": "  ^ Int.toString num ^ " }\n");
        print "redprl:> ";
        TextIO.inputLine TextIO.stdIn;
        printPart num list
      )
    end

  fun handleCommand command =
    case command of
      Execute code =>
        let
          val parsed = CharParser.parseString SignatureParser.parseSigExp code
        in
          case parsed of
            INL s => raise Fail s
          | INR sign =>
            let
              val elab = RefineElab.transport o ValidationElab.transport o BindSignatureElab.transport
              val sign' = elab sign
              val msg = Frontend.signToString sign'
            in
              if (String.size msg) > 650 then
                printInParts 650 (String.explode msg)
              else
                printMessage msg
            end
        end
      | Chunks amount =>
        let
          fun iter n s =
            case n of
              0 => s
            | k =>
              let
                val _ = print "redprl:> "
                val input = TextIO.inputLine TextIO.stdIn
              in
                case input of
                  SOME input => iter (n - 1) (s ^ (String.substring (input, 0, ((String.size input) - 1))))
                | NONE => iter (n - 1) s
              end
          val code = iter amount ""
        in
          handleCommand (Execute code)
        end
end
