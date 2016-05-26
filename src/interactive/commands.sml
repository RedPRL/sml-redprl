structure Commands =
struct
  val version = "0.0.1"

  open Json

  datatype command =
    Stop
  | GetVersion

  fun getCommand obj =
    case Json.getValueByKey obj "cmd" of
      SOME (Pair (_, String s)) =>
        (case s of
          "stop" => Stop
        | "getVersion" => GetVersion
        | _ => raise (Fail "Unknown command"))
    | _ => raise (Fail "Command is not specified")

  fun printMessage m = print ("{\"msg\": \"" ^ m ^ "\"}\n")

  fun handleCommand command =
    case command of
      Stop => OS.Process.exit OS.Process.success
    | GetVersion => printMessage version

end
