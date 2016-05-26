structure Interactive =
struct
  fun runLoop() =
    let
      val inputLine =
        case TextIO.inputLine TextIO.stdIn of
          SOME s => s
        | NONE => ""
      val jsonObj = Json.parse inputLine
      val command = Commands.getCommand jsonObj
    in
      Commands.handleCommand command;
      runLoop()
    end
    handle (Fail msg) => (Commands.printMessage msg; runLoop())
end
