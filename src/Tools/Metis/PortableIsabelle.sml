(*  Title:      Tools/Metis/PortableIsabelle.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010

Isabelle-specific setup for Metis. Based on "src/PortablePolyml.sml".
*)

structure Portable :> Portable =
struct

val ml = "isabelle"

fun pointerEqual (x : 'a, y : 'a) = pointer_eq (x, y)

local
  val lock = Mutex.mutex ();
in
  fun critical e () = Multithreading.synchronized "metis" lock e
end;

val randomWord = Random.nextWord
val randomBool = Random.nextBool
val randomInt = Random.nextInt
val randomReal = Random.nextReal

fun time f x = f x (* dummy *)

end

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
