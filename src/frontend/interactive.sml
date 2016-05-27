structure Interactive =
struct
  fun runLoop sessions =
    let
      val inputLine =
        case TextIO.inputLine TextIO.stdIn of
          SOME s => s
        | NONE => ""
      val jsonObj = Json.parse inputLine
      val command = Commands.getCommand jsonObj
      val newSessions = Commands.handleCommand command sessions
    in
      runLoop newSessions
    end
    handle (Fail msg) => (Commands.printMessage msg; runLoop sessions)
end
