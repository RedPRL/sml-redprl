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
    "A proof assistant based on Computational Type Theory\n" ^
    "Usage\n" ^
    "  jonprl <file>...\n" ^
    "  jonprl --help\n" ^
    "Options\n" ^
    "  --help            Print this message\n"

  fun main (_, args) =
    let
      val (opts, files) = List.partition (String.isPrefix "--") args
      val jonprlFiles = List.filter (String.isSuffix ".jonprl") files
      val mode = getMode opts
    in
      (case mode of
           PRINT_DEVELOPMENT => (map Frontend.processFile jonprlFiles; OS.Process.success)
         | HELP => (print helpMessage; OS.Process.success))
      handle E => (print (exnMessage E); OS.Process.failure)
    end

  val _ = OS.Process.exit (main (CommandLine.name (),
                                 CommandLine.arguments ()))

end
