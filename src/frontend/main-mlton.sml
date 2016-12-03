structure MainMLton =
struct
  val _ =
    OS.Process.exit
      (Main.main
        (CommandLine.name (),
         CommandLine.arguments ()))
end
