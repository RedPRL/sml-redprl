structure Sessions =
struct
  type sessionId = string
  type filename = string

  datatype session =
    Session of sessionId * (filename * AstSignature.sign) list

  (* Use current time as a session id *)
  fun generateSessionId() = Time.toString(Time.now())
end
