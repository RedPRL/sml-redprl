structure Main =
struct
  datatype mode =
      PRINT_DEVELOPMENT
    | HELP

  local
    fun go [] = PRINT_DEVELOPMENT
      | go ("--help" :: _) = HELP
      | go (_ :: xs) = go xs
  in
    fun getMode args = go args
  end

  val helpMessage =
    "A proof assistant for Computational Type Theory\n" ^
    "\n  ~ Long Live the Anti-Realist Struggle! ~ \n\n" ^
    "Usage\n" ^
    "  redprl <file>...\n" ^
    "  redprl --help\n" ^
    "Options\n" ^
    "  --help            Print this message\n"

  fun main (_, args) =
    let
      val (opts, files) = List.partition (String.isPrefix "--") args
      val redprlFiles = List.filter (fn x => String.isSuffix ".prl" x orelse String.isSuffix ".redprl" x) files
      val mode = getMode opts
    in
      case mode of
           PRINT_DEVELOPMENT => (map Frontend.processFile redprlFiles; OS.Process.success)
         | HELP => (print helpMessage; OS.Process.success)
    end
    handle E =>
      (print (exnMessage E);
       OS.Process.failure)

  val _ =
    OS.Process.exit
      (main
        (CommandLine.name (),
         CommandLine.arguments ()))

end
