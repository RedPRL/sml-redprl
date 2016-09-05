structure RedPrlLog :> REDPRL_LOG =
struct
  datatype level =
     INFO
   | WARN
   | FAIL

  fun formatMessage lvl (pos, msg) =
    let
      val pos' =
        case pos of
           SOME pos => Pos.toString pos
         | NONE => "[Unknown Location]"

      val prefix =
        case lvl of
           INFO => "Info"
         | WARN => "Warning"
         | FAIL => "Error"

      val lines = String.tokens (fn c => c = #"\n") msg
      val indented = List.map (fn l => "  " ^ l ^ "\n") lines
      val msg' = List.foldr op^ "" indented
    in
      pos' ^ " [" ^ prefix ^ "]:\n" ^ msg' ^"\n\n"
    end

  val streamForLevel =
    fn INFO => TextIO.stdOut
     | WARN => TextIO.stdOut
     | FAIL => TextIO.stdErr

  fun print lvl msg =
    let
      val stream = streamForLevel lvl
    in
      TextIO.output (stream, formatMessage lvl msg);
      TextIO.flushOut stream
    end
end
