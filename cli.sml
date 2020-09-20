fun fail s =
let
  val () = TextIO.output (TextIO.stdErr, s ^ "\n")
  open OS.Process
in
  exit failure
end

val usage =
let
  val name = CommandLine.name ()
in
  "usage: " ^ name ^ " [filename]"
end

val () =
let
  val args = CommandLine.arguments ()
  val stream = Stream.fromTextInstream $ TextIO.openIn $ hd args
in
  case main stream of
       Ok(s, e) =>
         TextIO.print ("signature: " ^ Show.show_sig s ^ "\n") before
         TextIO.print ("value    : " ^ Dyn.show 0 e ^ "\n")
     | Err s => fail s
end handle IO.Io r    => fail ("cannot open: " ^ #name r)
         | List.Empty => fail usage
