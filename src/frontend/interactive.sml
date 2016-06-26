structure Interactive =
struct
  fun runLoop sessions =
    case TextIO.inputLine TextIO.stdIn of
      SOME inputLine =>
        (let
          val jsonObj = Json.parse inputLine
          val command = Commands.getCommand jsonObj
          val newSessions = Commands.handleCommand command sessions
        in
          runLoop newSessions
        end
        handle E => (Commands.printMessage (exnMessage E); runLoop sessions))
    | NONE => OS.Process.success
end
