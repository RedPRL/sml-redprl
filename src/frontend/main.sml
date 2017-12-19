structure Main =
struct
  datatype mode =
      PRINT_DEVELOPMENT of string list
    | FROM_STDIN of string option
    | HELP

  local
    fun extractArg n x =
      case explode (String.extract (x, n, NONE)) of
         #"=" :: rest => SOME (implode rest)
       | _ => NONE
    fun setWidth x = Option.app (fn n => Config.maxWidth := n) (Option.mapPartial Int.fromString x)
    fun go [] mode = mode
      | go ("--help" :: xs) _ = go xs (SOME HELP)
      | go (x :: xs) mode =
        if String.isPrefix "--from-stdin" x
        then go xs (SOME (FROM_STDIN (extractArg (String.size "--from-stdin") x)))
        else if String.isPrefix "--width=" x
        then (setWidth (extractArg (String.size "--width") x); go xs mode)
        else
          (case mode of
              NONE => go xs (SOME (PRINT_DEVELOPMENT [x]))
            | SOME (PRINT_DEVELOPMENT files) => go xs (SOME (PRINT_DEVELOPMENT (files @ [x])))
            | SOME _ => go xs mode)
  in
    fun getMode args = Option.getOpt (go args NONE, HELP)
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
    "  --width=cols              Set output width to cols (default: 80)\n" ^
    "  --from-stdin[=filename]   Read signature from stdin with optional diagnostic filename\n"

  fun toExitStatus b = if b then OS.Process.success else OS.Process.failure

  fun main (_, args) =
    Debug.wrap (fn _ =>
      case getMode args of
         PRINT_DEVELOPMENT files => toExitStatus (List.all Frontend.processFile files)
       | FROM_STDIN ofile => toExitStatus (Frontend.processStream (Option.getOpt (ofile, "<stdin>")) TextIO.stdIn)
       | HELP => (print helpMessage; OS.Process.success))
    handle E =>
      (FppRenderPlainText.render TextIO.stdErr (FinalPrinter.execPP (RedPrlError.format E));
       OS.Process.failure)
end
