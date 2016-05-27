structure Sessions =
struct
  datatype session =
    (* sessionId,  *)
    Session of string

  fun generateSessionId() = "new session id"
end
