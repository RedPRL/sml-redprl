structure Interactive =
struct
  fun runLoop' sign =
    let
      val _ = print "redprl:> "
      val input = TextIO.inputLine TextIO.stdIn
    in
      case input of
        SOME input =>
          (let
            val jsonObj = Json.parse input
            val command = Commands.getCommand jsonObj
            val newSign = Commands.handleCommand sign command
          in
            runLoop' newSign
          end
          handle E => (Commands.printMessage (exnMessage E); runLoop' sign))
      | NONE => OS.Process.success
    end

  val runLoop = runLoop' AbtSignature.Telescope.empty
end
