(*  Title:      HOL/Tools/Mirabelle/mirabelle_util.ML
    Author:     Martin Desharnais, MPI-INF Saarbruecken
*)

(* Pseudorandom number generator *)
signature PRNG = sig
  type state
  val initialize : int -> state
  val next : state -> int * state
end

(* Pseudorandom algorithms *)
signature PRNG_ALGORITHMS = sig
  include PRNG
  val shuffle : state -> 'a list -> 'a list * state
end

functor PRNG_Algorithms(PRNG : PRNG) : PRNG_ALGORITHMS = struct

open PRNG

fun shuffle prng_state xs =
  fold_map (fn x => fn prng_state =>
    let
      val (n, prng_state') = next prng_state
    in ((n, x), prng_state') end) xs prng_state
  |> apfst (sort (int_ord o apply2 fst))
  |> apfst (map snd)

end

(* multiplicative linear congruential generator *)
structure MLCG_PRNG : PRNG = struct
  (* The modulus is implicitly 2^64 through using Word64.
     The multiplier and increment are the same as Newlib and Musl according to Wikipedia.
     See: https://en.wikipedia.org/wiki/Linear_congruential_generator#Parameters_in_common_use
   *)
  val multiplier = Word64.fromInt 6364136223846793005
  val increment = Word64.fromInt 1

  type state = Word64.word

  val initialize = Word64.fromInt

  fun next s =
    let
      open Word64
      val s' = multiplier * s + increment
    in
      (toInt s', s')
    end
end

structure MLCG = PRNG_Algorithms(MLCG_PRNG)
