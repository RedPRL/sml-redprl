structure Commands =
struct
  val version = "0.0.1"

  structure J = Json
  open Sum

  datatype command =
    Execute of string

  fun getValueByKeyOrFail obj key =
    case J.getValueByKey obj key of
      SOME (J.String s) => s
    | NONE => raise Fail ("Missing attribute: " ^ key)
    | _ => raise Fail ("Wrong type of attribute:" ^ key)

  fun getCommand obj =
    case J.getValueByKey obj "cmd" of
      SOME (J.String s) =>
        (case s of
          "execute" => Execute (getValueByKeyOrFail obj "code")
        | _ => raise (Fail "Unknown command"))
    | _ => raise (Fail "Command is not specified")

  fun printKeyValue k v = print ("{\"" ^ k ^ "\": \"" ^ v ^ "\"}\n")
  val printMessage = printKeyValue "msg"

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
            in
              printMessage (Frontend.signToString sign')
            end
        end
end
