(*  Title:      Pure/General/random_word.ML
    ID:         $Id$
    Author:     Makarius

Simple generator for pseudo-random numbers, using unboxed word
arithmetic only.  Unprotected concurrency introduces some true
randomness.
*)

signature RANDOM_WORD =
sig
  val range: word
  val next: unit -> word
  val next_bit: unit -> bool
end;

structure RandomWord: RANDOM_WORD =
struct

(*minimal length of unboxed words on all known platforms*)
val bits = 30;
val _ = Word.wordSize >= bits orelse raise Fail ("Bad platform word size");

val range = 0wx40000000;
val mask = range - 0w1;
val max_bit = Word.>> (range, 0w1);

(*multiplier according to Borosh and Niederreiter (for m = 2^30),
  cf. http://random.mat.sbg.ac.at/~charly/server/server.html*)
val a = 0w777138309;

(*generator*)
val rand = ref 0w0;
fun next () = (rand := Word.andb (a * ! rand + 0w1, mask); ! rand);
fun next_bit () = Word.andb (next (), max_bit) = 0w0;

end;

