structure MlFrontend =
struct
  structure Lex = MetalanguageLex and Parse = MetalanguageParse

  fun @@ (f, x) = f x
  infixr @@

  (* Cribbed again from Chris Martens / Ceptre *)

  fun coordinate eoln coord s =
    Stream.lazy (fn () =>
      case Stream.front s of
         Stream.Nil => Stream.Nil
       | Stream.Cons (x, s') =>
         let
           val coord' = if eoln s then Coord.nextline coord else Coord.nextchar coord
         in
           Stream.Cons ((coord, x), coordinate eoln coord' s')
         end)

  fun eol stream = 
    case Stream.front stream of
       Stream.Cons (#"\n", _) => true
     | Stream.Cons (#"\v", _) => true
     | Stream.Cons (#"\f", _) => true
     | Stream.Cons (#"\r", stream) => 
       (case Stream.front stream of
           Stream.Cons (#"\n", _) => false
         | _ => true)
      | _ => false

  fun parseFile s =
    let
      val textStream = TextIO.openIn s
      val str = Stream.eager o Lex.lexmain o coordinate eol (Coord.init s) @@ Stream.fromTextInstream textStream
      val (tops, _) =
        Parse.parse str handle exn =>
          (TextIO.closeIn textStream;
           RedPrlLog.print RedPrlLog.FAIL (RedPrlError.annotation exn, RedPrlError.format exn);
           raise exn)
    in
      tops
      before TextIO.closeIn textStream
    end
end