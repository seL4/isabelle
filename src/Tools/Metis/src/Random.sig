(*  Title:      Tools/random_word.ML
    Author:     Makarius

Simple generator for pseudo-random numbers, using unboxed word
arithmetic only.  Unprotected concurrency introduces some true
randomness.
*)

signature Random =
sig

  val nextWord : unit -> word

  val nextBool : unit -> bool

  val nextInt : int -> int  (* k -> [0,k) *)

  val nextReal : unit -> real  (* () -> [0,1) *)

end;
