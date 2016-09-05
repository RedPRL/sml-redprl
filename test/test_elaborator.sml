structure Main =
struct
  val _ = print "ASDFADF!"
  val _ = raise Fail "ASDFASDF"

  val status =
    if Frontend.processFile "test/test.prl" then
      OS.Process.success
    else
      OS.Process.failure

  val _ = OS.Process.exit status
end
