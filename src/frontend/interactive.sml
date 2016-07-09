structure Interactive =
struct
  fun runLoop() =
    let
      val _ = print "> "
      val input = TextIO.inputLine TextIO.stdIn
    in
      case input of
        SOME input =>
          (let
            val jsonObj = Json.parse input
            val command = Commands.getCommand jsonObj
            val newSessions = Commands.handleCommand command
          in
            runLoop()
          end
          handle E => (Commands.printMessage (exnMessage E); runLoop()))
      | NONE => OS.Process.success
    end
end
