structure Commands =
struct
  val version = "0.0.1"

  structure J = Json
  open Sessions
  open Sum

  datatype command =
    Stop
  | GetVersion
  | NewSession of string option
  | CloseSession of sessionId
  | AddFiles of sessionId * (filename list)

  fun getValueByKeyOrFail obj key =
    case J.getValueByKey obj key of
      SOME v => v
    | NONE => raise Fail ("Missing attribute: " ^ key)

  fun getCommand obj =
    case J.getValueByKey obj "cmd" of
      SOME (J.String s) =>
        (case s of
          "stop" => Stop
        | "get_version" => GetVersion
        | "new_session" =>
          (case J.getValueByKey obj "name" of
            SOME (J.String s) => NewSession (SOME s)
          | _ => NewSession NONE)
        | "close_session" =>
          (case getValueByKeyOrFail obj "session_id" of
            J.String s => CloseSession s
          | _ => raise (Fail "Wrong type of sessionId"))
        | "add_files" =>
          let
            val sessionId = getValueByKeyOrFail obj "session_id"
            val filenames = getValueByKeyOrFail obj "filenames"
          in
            case (sessionId, filenames) of
              (J.String s, J.Array a) => AddFiles (s, (List.map (fn (J.String s) => s) a))
            | _ => raise (Fail "Wrong type of arguments")
          end
        | _ => raise (Fail "Unknown command"))
    | _ => raise (Fail "Command is not specified")

  fun printKeyValue k v = print ("{\"" ^ k ^ "\": \"" ^ v ^ "\"}\n")
  val printMessage = printKeyValue "msg"

  fun handleCommand command sessions =
    case command of
      Stop => OS.Process.exit OS.Process.success
    | GetVersion => (printMessage version; sessions)
    | NewSession name =>
      let
        val sessionId = case name of
          SOME s => s
        | NONE => generateSessionId()
      in
        printKeyValue "session_id" sessionId; (Session (sessionId, []))::sessions
      end
    | CloseSession s =>
      let
        val newSessions = List.filter (fn (Session (sessionId, _)) => not (sessionId = s)) sessions
      in
        printMessage "Session has been closed";
        newSessions
      end
    | AddFiles (sessionId, filenames) =>
      let
        val pairs = List.map (fn filename =>
          let
            val input = TextIO.inputAll (TextIO.openIn filename)
            val parsed = CharParser.parseString SignatureParser.parseSigExp input
          in
            case parsed of
              INL s => raise Fail ("Parsing of " ^ filename ^ " has failed: " ^ s)
            | INR sign => (filename, sign)
          end) filenames
      in
        printMessage "Files have been added";
        List.foldl (fn ((Session (sId, l)), y) =>
          (if sId = sessionId then Session (sId, pairs@l)
            else Session (sId, l)
          )::y) [] sessions
      end
end
