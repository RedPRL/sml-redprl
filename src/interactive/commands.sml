structure Commands =
struct
  val version = "0.0.1"

  open Json
  open Sessions

  datatype command =
    Stop
  | GetVersion
  | NewSession
  | CloseSession of string (* sessionId *)

  fun getValueByKeyOrFail obj key =
    case Json.getValueByKey obj key of
      SOME (Pair (_, String s)) => s
    | _ => raise Fail ("Missing attribute: " ^ key)

  fun getCommand obj =
    case Json.getValueByKey obj "cmd" of
      SOME (Pair (_, String s)) =>
        (case s of
          "stop" => Stop
        | "getVersion" => GetVersion
        | "newSession" => NewSession
        | "closeSession" => CloseSession (getValueByKeyOrFail obj "sessionId")
        | _ => raise (Fail "Unknown command"))
    | _ => raise (Fail "Command is not specified")

  fun printMessage m = print ("{\"msg\": \"" ^ m ^ "\"}\n")

  fun handleCommand command sessions =
    case command of
      Stop => OS.Process.exit OS.Process.success
    | GetVersion => (printMessage version; sessions)
    | NewSession =>
      let
        val sessionId = generateSessionId()
      in
        (Session sessionId)::sessions
      end
    | CloseSession s => (print s; sessions)

end
