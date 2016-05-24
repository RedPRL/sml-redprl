structure Interactive =
struct
  open JsonWrapper

  fun handleCommand command =
    case command of
      SOME (Pair (_, String s)) => print s
    | _ => raise (Fail "Command is not specified")

  fun runLoop() =
    let
      val inputLine =
        case TextIO.inputLine TextIO.stdIn of
          SOME s => s
        | NONE => ""
      val jsonObj = Json.parse inputLine
      val command = getValueByKey jsonObj "cmd"
    in
      handleCommand command;
      runLoop()
    end
    handle (Fail msg) => (print (msg ^ "\n"); runLoop())
end
