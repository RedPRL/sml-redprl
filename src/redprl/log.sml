structure RedPrlLogBasis :> REDPRL_LOG =
struct
  datatype level =
     INFO
   | WARN
   | DUMP
   | FAIL
   | TRACE

  fun formatMessage lvl (pos, msg) : (int, unit) FppTypes.output = raise Fail "TODO"
(*  
    let
      val pos' =
        case pos of
           SOME pos => Pos.toString pos
         | NONE => "[Unknown Location]"

      val prefix =
        case lvl of
           INFO => "Info"
         | DUMP => "Output"
         | WARN => "Warning"
         | FAIL => "Error"
         | TRACE => "Trace"

      val lines = String.fields (fn c => c = #"\n") msg
      val indented = List.map (fn l => "  " ^ l ^ "\n") lines
      val msg' = List.foldr op^ "" indented
    in
      pos' ^ " [" ^ prefix ^ "]:\n" ^ msg' ^"\n\n"
    end*)

  val streamForLevel =
    fn INFO => TextIO.stdOut
     | DUMP => TextIO.stdOut
     | WARN => TextIO.stdOut
     | FAIL => TextIO.stdErr
     | TRACE => TextIO.stdOut

  fun print lvl msg =
    let
      val stream = streamForLevel lvl
    in
      FppRenderPlainText.render stream (formatMessage lvl msg);
      TextIO.flushOut stream
    end
end


functor RedPrlLogUtil (L : REDPRL_LOG) : REDPRL_LOG_UTIL= 
struct
  open L

  fun trace msg = 
    () 
    (*print TRACE (NONE, msg)*)
end

structure RedPrlLog = RedPrlLogUtil (RedPrlLogBasis)