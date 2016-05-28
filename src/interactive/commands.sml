structure Commands =
struct
  val version = "0.0.1"

  open Json
  open Sessions
  open Sum

  datatype command =
    Stop
  | GetVersion
  | NewSession
  | CloseSession of sessionId
  | AddFiles of sessionId * (filename list)

  fun getValueByKeyOrFail obj key =
    case Json.getValueByKey obj key of
      SOME (Pair (_, v)) => v
    | _ => raise Fail ("Missing attribute: " ^ key)

  fun getCommand obj =
    case Json.getValueByKey obj "cmd" of
      SOME (Pair (_, String s)) =>
        (case s of
          "stop" => Stop
        | "getVersion" => GetVersion
        | "newSession" => NewSession
        | "closeSession" =>
          (case getValueByKeyOrFail obj "sessionId" of
            String s => CloseSession s
          | _ => raise (Fail "Wrong type of sessionId"))
        | "addFiles" =>
          let
            val sessionId = getValueByKeyOrFail obj "sessionId"
            val filenames = getValueByKeyOrFail obj "filenames"
          in
            case (sessionId, filenames) of
              (String s, Array a) => AddFiles (s, (List.map (fn (String s) => s) a))
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
    | NewSession =>
      let
        val sessionId = generateSessionId()
      in
        printKeyValue "sessionId" sessionId; (Session (sessionId, []))::sessions
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
