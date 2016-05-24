structure JsonWrapper =
struct

  datatype jsonValue =
    Pair of (string * jsonValue)
  | Array of jsonValue list
  | Null
  | Float of real
  | String of string
  | Bool of bool
  | Int of int

  structure JSONValueCallbacks =
  struct
     type json_data = jsonValue

     fun json_object l = Array l
     fun json_pair p = Pair p
     fun json_array l = Array l
     fun json_value x = x
     fun json_string s = String s
     val json_int = Int
     val json_real = Float
     val json_bool = Bool
     fun json_null () = Null

     fun error_handle (msg,pos,data) =
        raise Fail ("Error: " ^ msg ^ " near " ^ Int.toString pos)
  end

  structure Json = JSONParser (JSONValueCallbacks);

  fun getValueByKey obj key =
    case obj of
      Array l => List.find (fn (Pair (k, v)) => k = key) l
    | _ => NONE

end
