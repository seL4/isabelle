(*  Title:      Tools/random_word.ML
    Author:     Makarius

Simple generator for pseudo-random numbers, using unboxed word
arithmetic only.  Unprotected concurrency introduces some true
randomness.
*)

structure Random :> Random =
struct

(* random words: 0w0 <= result <= max_word *)

(*minimum length of unboxed words on all supported ML platforms*)
val _ = Word.wordSize >= 30
  orelse raise Fail ("Bad platform word size");

val max_word = 0wx3FFFFFFF;
val top_bit = 0wx20000000;

(*multiplier according to Borosh and Niederreiter (for modulus = 2^30),
  see http://random.mat.sbg.ac.at/~charly/server/server.html*)
val a = 0w777138309;
fun step x = Word.andb (a * x + 0w1, max_word);

fun change r f = r := f (!r);
local val rand = (*Unsynchronized.*)ref 0w1
in fun nextWord () = ((*Unsynchronized.*)change rand step; ! rand) end;

(*NB: higher bits are more random than lower ones*)
fun nextBool () = Word.andb (nextWord (), top_bit) = 0w0;


(* random integers: 0 <= result < k *)

val max_int = Word.toInt max_word;

fun nextInt k =
  if k <= 0 orelse k > max_int then raise Fail ("next_int: out of range")
  else if k = max_int then Word.toInt (nextWord ())
  else Word.toInt (Word.mod (nextWord (), Word.fromInt k));

(* random reals: 0.0 <= result < 1.0 *)

val scaling = real max_int + 1.0;
fun nextReal () = real (Word.toInt (nextWord ())) / scaling;

end;
