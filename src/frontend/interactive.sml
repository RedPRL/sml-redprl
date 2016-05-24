structure Interactive =
struct
  val version = "0.0.1"

  open JsonWrapper

  datatype command =
    Stop
  | GetVersion

  fun getCommand obj =
    case getValueByKey obj "cmd" of
      SOME (Pair (_, String s)) =>
        (case s of
          "stop" => Stop
        | "getVersion" => GetVersion
        | _ => raise (Fail "Unknown command"))
    | _ => raise (Fail "Command is not specified")

  fun printMessage m = print ("{\"msg\": \"" ^ m ^ "\"}")

  fun handleCommand command =
    case command of
      Stop => OS.Process.exit OS.Process.success
    | GetVersion => printMessage version

  fun runLoop() =
    let
      val inputLine =
        case TextIO.inputLine TextIO.stdIn of
          SOME s => s
        | NONE => ""
      val jsonObj = Json.parse inputLine
      val command = getCommand jsonObj
    in
      handleCommand command;
      runLoop()
    end
    handle (Fail msg) => (printMessage msg; runLoop())
end
