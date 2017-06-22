structure Main =
struct
  datatype mode =
      PRINT_DEVELOPMENT
    | FROM_STDIN of string option
    | HELP

  local
    fun go [] = PRINT_DEVELOPMENT
      | go ("--help" :: _) = HELP
      | go (x :: xs) =
        if String.isPrefix "--from-stdin" x
        then let
          val rest = String.extract (x, String.size "--from-stdin", NONE)
          val fileName = case explode rest of
                           #"=" :: rest => SOME (implode rest)
                         | _ => NONE
        in
          FROM_STDIN fileName
        end
        else go xs
  in
    fun getMode args = go args
  end

  val helpMessage =
    "                                A proof assistant for Computational Type Theory           \n" ^
    "             `.                                                                           \n" ^
    "              `--`        %%%%%%%    %%%%%%%%   %%%%%%%    %%%%%%%    %%%%%%%    %%       \n" ^
    "      `-:::.    -:-       %%    %%   %%         %%    %%   %%    %%   %%    %%   %%       \n" ^
    "    `-::::.      -:-      %%    %%   %%         %%    %%   %%    %%   %%    %%   %%       \n" ^
    "    .::-`-::.     ::.     %%%%%%%    %%%%%%     %%    %%   %%%%%%%    %%%%%%%    %%       \n" ^
    "          `-::.   ::-     %%    %%   %%         %%    %%   %%         %%    %%   %%       \n" ^
    "            `:::.-::`     %%    %%   %%         %%    %%   %%         %%    %%   %%       \n" ^
    "     `-:::-...-::::.      %%    %%   %%%%%%%%   %%%%%%%    %%         %%    %%   %%%%%%%% \n" ^
    "   .::-` .-:::::-:::.                                                                     \n" ^
    "  .::.            .::.                    ~ Uphold Cubical Thought! ~                     \n" ^
    "\nUsage\n" ^
    "  redprl <file>...\n" ^
    "  redprl --help\n" ^
    "Options\n" ^
    "  --help                    Print this message\n" ^
    "  --from-stdin[=filename]   Read signature from stdin with optional diagnostic filename\n"

  fun toExitStatus b = if b then OS.Process.success else OS.Process.failure

  fun main (_, args) =
    Debug.wrap (fn _ =>
      let
        val (opts, files) = List.partition (String.isPrefix "--") args
        val redprlFiles = List.filter (fn x => String.isSuffix ".prl" x orelse String.isSuffix ".redprl" x) files
        val mode = getMode opts
      in
        case mode of
             PRINT_DEVELOPMENT => toExitStatus (List.all Frontend.processFile redprlFiles)
           | FROM_STDIN ofile => toExitStatus (Frontend.processStream (Option.getOpt (ofile, "<stdin>")) TextIO.stdIn)
           | HELP => (print helpMessage; OS.Process.success)
      end)
    handle E =>
      (FppRenderPlainText.render TextIO.stdErr (FinalPrinter.execPP (RedPrlError.format E));
       OS.Process.failure)
end
