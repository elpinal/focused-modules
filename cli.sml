val ex_filename = ",example.fm"

fun fail s = TextIO.output (TextIO.stdErr, s ^ "\n")

val stream = Stream.fromTextInstream $ TextIO.openIn ex_filename

val () =
let in
  case main stream of
       Ok(s, e) =>
         TextIO.print ("signature: " ^ Show.show_sig s ^ "\n") before
         TextIO.print ("value    : " ^ Dyn.show 0 e ^ "\n")
     | Err s => fail s
end handle IO.Io r => fail ("cannot open: " ^ #name r)
