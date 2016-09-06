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
    "\n  ~ Uphold Cubical Thought! ~ \n\n" ^
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
           PRINT_DEVELOPMENT => if List.all Frontend.processFile redprlFiles then OS.Process.success else OS.Process.failure
         | HELP => (print helpMessage; OS.Process.success)
    end
    handle E =>
      (print (RedPrlError.format E);
       OS.Process.failure)

  val _ =
    OS.Process.exit
      (main
        (CommandLine.name (),
         CommandLine.arguments ()))

end
