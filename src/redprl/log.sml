structure RedPrlLogBasis :> REDPRL_LOG =
struct
  datatype level =
     INFO
   | WARN
   | DUMP
   | FAIL
   | TRACE

  fun formatMessage lvl (pos, msg : FinalPrinter.doc) : FinalPrinter.doc =
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

      val header =
        Fpp.hsep 
          [Fpp.text pos',
           Fpp.seq [Fpp.Atomic.squares (Fpp.text prefix), Fpp.Atomic.colon]]

    in
      Fpp.seq [Fpp.nest 4 (Fpp.vsep [header, msg]), Fpp.hardLine, Fpp.hardLine]
    end

  val streamForLevel =
    fn INFO => TextIO.stdOut
     | DUMP => TextIO.stdOut
     | WARN => TextIO.stdOut
     | FAIL => TextIO.stdErr
     | TRACE => TextIO.stdOut

  fun print lvl msg =
    let
      val stream = streamForLevel lvl
      val doc = formatMessage lvl msg
      val output = FinalPrinter.execPP doc
    in
      FppRenderPlainText.render stream output;
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