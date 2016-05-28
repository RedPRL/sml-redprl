structure Sessions =
struct
  type sessionId = string

  datatype session =
    (* sessionId,  *)
    Session of sessionId

  (* Use current time as a session id *)
  fun generateSessionId() = Time.toString(Time.now())
end
