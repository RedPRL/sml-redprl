(*******************************************************************************
*  Standard ML JSON parser
*  Copyright (C) 2010  Gian Perrone
*
*  This program is free software: you can redistribute it and/or modify
*  it under the terms of the GNU General Public License as published by
*  the Free Software Foundation, either version 3 of the License, or
*  (at your option) any later version.
*
*  This program is distributed in the hope that it will be useful,
*  but WITHOUT ANY WARRANTY; without even the implied warranty of
*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*  GNU General Public License for more details.
*
*  You should have received a copy of the GNU General Public License
*  along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************)

signature JSON_CALLBACKS =
sig
   type json_data

   val json_object   : json_data list -> json_data
   val json_pair     : string * json_data -> json_data
   val json_array    : json_data list -> json_data
   val json_value    : json_data -> json_data
   val json_string   : string -> json_data
   val json_int      : int -> json_data
   val json_real     : real -> json_data
   val json_bool     : bool -> json_data
   val json_null     : unit -> json_data

   val error_handle  : string * int * string -> json_data
end

functor JSONParser (Callbacks : JSON_CALLBACKS) =
struct
   type json_data = Callbacks.json_data

   exception JSONParseError of string * int

   val inputData = ref ""
   val inputPosition = ref 0

   fun isDigit () = Char.isDigit (String.sub (!inputData,0))

   fun ws () = while (String.isPrefix " " (!inputData) orelse
                      String.isPrefix "\n" (!inputData) orelse
                      String.isPrefix "\t" (!inputData) orelse
                      String.isPrefix "\r" (!inputData))
               do (inputData := String.extract (!inputData, 1, NONE))

   fun peek () = String.sub (!inputData,0)
   fun take () =
      String.sub (!inputData,0) before
         inputData := String.extract (!inputData, 1, NONE)

   fun matches s = (ws(); String.isPrefix s (!inputData))
   fun consume s =
      if matches s then
         (inputData := String.extract (!inputData, size s, NONE);
          inputPosition := !inputPosition + size s)
                   else
         raise JSONParseError ("Expected '"^s^"'", !inputPosition)

   fun parseObject () =
      if not (matches "{") then
         raise JSONParseError ("Expected '{'", !inputPosition)
      else
         (consume "{"; ws ();
          if matches "}" then Callbacks.json_object [] before consume "}"
          else
            (Callbacks.json_object (parseMembers ())
               before (ws (); consume "}")))

   and parseMembers () =
      parsePair () ::
         (if matches "," then (consume ","; parseMembers ()) else [])

   and parsePair () =
      Callbacks.json_pair (parseString (),
         (ws(); consume ":"; parseValue ()))

   and parseArray () =
      if not (matches "[") then
         raise JSONParseError ("Expected '['", !inputPosition)
      else
        (consume "[";
         if matches "]" then
            Callbacks.json_array [] before consume "]"
         else
            Callbacks.json_array (parseElements ()) before (ws (); consume "]"))

   and parseElements () =
      parseValue () ::
         (if matches "," then (consume ","; parseElements ()) else [])

   and parseValue () =
      Callbacks.json_value (
         if matches "\"" then Callbacks.json_string (parseString ()) else
         if matches "-" orelse isDigit () then parseNumber () else
         if matches "true" then Callbacks.json_bool true else
         if matches "false" then Callbacks.json_bool false else
         if matches "null" then Callbacks.json_null () else
         if matches "[" then parseArray () else
         if matches "{" then parseObject () else
         raise JSONParseError ("Expected value", !inputPosition))

   and parseString () =
        (ws () ;
         consume ("\"") ;
         parseChars () before consume "\"")

   and parseChars () =
   let
      fun pickChars s =
         if peek () = #"\"" (* " *) then s else
            pickChars (s ^ String.str (take ()))
   in
      pickChars ""
   end

   and parseNumber () =
   let
      val i = parseInt ()
   in
      if peek () = #"e" orelse peek () = #"E" then
         Callbacks.json_int (valOf (Int.fromString (i^parseExp())))
      else if peek () = #"." then
         let
            val f = parseFrac()

            val f' = if peek() = #"e" orelse peek() = #"E" then
                        i ^ f ^ parseExp ()
                     else i ^ f
         in
            Callbacks.json_real (valOf (Real.fromString f'))
         end
      else Callbacks.json_int (valOf (Int.fromString i))
   end

   and parseInt () =
   let
      val f =
         if peek () = #"0" then
            raise JSONParseError ("Invalid number", !inputPosition)
         else if peek () = #"-" then (take (); "~")
         else String.str (take ())
   in
      f ^ parseDigits ()
   end

   and parseDigits () =
   let
      val r = ref ""
   in
      (while Char.isDigit (peek ()) do
         r := !r ^ String.str (take ());
       !r)
   end

   and parseFrac () =
      (consume "." ;
         "." ^ parseDigits ())

   and parseExp () =
   let
      val _ =
         if peek () = #"e" orelse
            peek () = #"E" then take ()
         else
            raise JSONParseError ("Invalid number", !inputPosition)

      val f = if peek () = #"-" then (take (); "~")
               else if peek () = #"+" then (take (); "")
               else ""
   in
      "e" ^ f ^ parseDigits ()
   end

   fun parse s =
      (inputData := s ;
       inputPosition := 0 ;
       parseObject ()) handle JSONParseError (m,p) =>
         Callbacks.error_handle (m,p,!inputData)
end

structure JSONPrettyPrintCallbacks =
struct
   type json_data = string

   fun json_object l =
      "{\n   " ^
      String.concatWith "\n   " l ^
      "}\n"
   fun json_pair (k,v) = k ^": "^v
   fun json_array l = "[" ^ String.concatWith ", " l ^ "]"
   fun json_value x = x
   fun json_string s = "\"" ^ s ^ "\""
   val json_int = Int.toString
   val json_real = Real.toString
   val json_bool = Bool.toString
   fun json_null () = "null"

   fun error_handle (msg,pos,data) =
      raise Fail ("Error: " ^ msg ^ " near " ^ Int.toString pos)
end
