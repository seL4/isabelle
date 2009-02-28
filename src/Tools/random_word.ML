(*  Title:      Tools/random_word.ML
    Author:     Makarius

Simple generator for pseudo-random numbers, using unboxed word
arithmetic only.  Unprotected concurrency introduces some true
randomness.
*)

signature RANDOM_WORD =
sig
  val max_word: word
  val step: word -> word
  val next_word: unit -> word
  val next_bool: unit -> bool
  val next_int: int -> int -> int
  val next_real: unit -> real
  val pick_any: 'a list -> 'a
  val pick_weighted: (int * 'a) list -> 'a
end;

structure RandomWord: RANDOM_WORD =
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

local val rand = ref 0w1
in fun next_word () = (change rand step; ! rand) end;

(*NB: higher bits are more random than lower ones*)
fun next_bool () = Word.andb (next_word (), top_bit) = 0w0;


(* random integers: i <= result <= j *)

val max_int = Word.toInt max_word;

fun next_int i j =
  let val k = j - i in
    if k < 0 orelse k > max_int then raise Fail ("next_int: out of range")
    else if k < max_int then i + Word.toInt (Word.mod (next_word (), Word.fromInt (k + 1)))
    else i + Word.toInt (next_word ())
  end;


(* random reals: 0.0 <= result < 1.0 *)

val scaling = real max_int + 1.0;
fun next_real () = real (Word.toInt (next_word ())) / scaling;


(* random list elements *)

fun pick_any [] = raise Empty
  | pick_any xs = nth xs (next_int 0 (length xs - 1));

fun pick_weighted xs =
  let
    val total = fold (fn (k, _) => fn i =>
      if k < 0 then raise Fail ("Bad weight: " ^ string_of_int k) else k + i) xs 0;
    fun pick n ((k, x) :: xs) =
        if n <= k then x else pick (n - k) xs
      | pick _ [] = raise Empty;
  in if total = 0 then raise Empty else pick (next_int 1 total) xs end;

end;

