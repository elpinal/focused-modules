val css = "<link href='./css/main.css' rel='stylesheet'>"
val head = "<head><title>Focused Modules</title>" ^ css ^ "</head>"

infix ^/

fun x ^/ y = x ^ "\n" ^ y

val sample =
     "circ"
  ^/ "bind 'a/B <-"
  ^/ "  let 'bool/M = (| forall 'a : Type. 'a -> 'a -> 'a |) in"
  ^/ "  let id = poly ('a : Type) -> fun (x : 'a) -> x in"
  ^/ "  let tru = poly ('a : Type) -> fun (t : 'a) -> fun (f : 'a) -> t in"
  ^/ "  let fls = poly ('a : Type) -> fun (t : 'a) -> fun (f : 'a) -> f in"
  ^/ "  let not = fun (b : 'bool) ->"
  ^/ "    poly ('a : Type) -> fun (t : 'a) -> fun (f : 'a) -> b ['a] f t"
  ^/ "  in"
  ^/ "  circ"
  ^/ "  ((| 'bool |), <| ((tru, fls), not) |>)"
  ^/ "  :>"
  ^/ "  ('a : (|Type|)) * <| ('a * 'a) * ('a -> 'a) |>"
  ^/ "in"
  ^/ "ret (snd B)"

val p1 = "<p>Read the excellent paper by Karl Crary! <a href='http://www.cs.cmu.edu/~crary/papers/2020/exsig.pdf'>A focused solution to the avoidance problem</a></p>"

val _ = print ("<html>" ^ head ^ "<body><main><h1>Focused Modules"
               ^ "</span></h1><textarea cols=100 rows=22 id='textbox'>" ^ sample ^ "</textarea>"
               ^ "<ul id=output>?</ul>" ^ p1 ^ "</main><footer>Powered by <a href='http://smlserver.org/smltojs/'>SMLtoJs</a></footer></body></html>")

open Rwp
val input : string b = textField "textbox"

fun f x =
let val () = TVar.reset () in
  case main (Stream.fromString x) handle _ => Err("error") of
       Ok(s, e) =>
         "<li>signature: " ^ Show.show_sig s ^ "</li>" ^
         "<li>value: " ^ Dyn.show 0 e    ^ "</li>"
     | Err(s) => s
end

val _ = insertDOM "output" (arr f input)
