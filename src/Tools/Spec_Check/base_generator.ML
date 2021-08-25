(*  Title:      Tools/Spec_Check/base_generator.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Basic random generators.
*)

signature BASE_GENERATOR =
sig

type rand
type 'a gen = rand -> 'a * rand
type ('a, 'b) co = 'a -> 'b gen -> 'b gen

val new : unit -> rand
val range : int * int -> rand -> int * rand
type ('a, 'b) reader = 'b -> ('a * 'b) option

val lift : 'a -> 'a gen
val select : 'a vector -> 'a gen
val choose : 'a gen vector -> 'a gen
val choose' : (int * 'a gen) vector -> 'a gen
val selectL : 'a list -> 'a gen
val chooseL : 'a gen list -> 'a gen
val chooseL' : (int * 'a gen) list -> 'a gen
val filter : ('a -> bool) -> 'a gen -> 'a gen

val zip : ('a gen * 'b gen) -> ('a * 'b) gen
val zip3 : ('a gen * 'b gen * 'c gen) -> ('a * 'b * 'c) gen
val zip4 : ('a gen * 'b gen * 'c gen * 'd gen) -> ('a * 'b * 'c * 'd) gen
val map : ('a -> 'b) -> 'a gen -> 'b gen
val map2 : ('a * 'b -> 'c) -> ('a gen * 'b gen) -> 'c gen
val map3 : ('a * 'b * 'c -> 'd) -> ('a gen * 'b gen * 'c gen) -> 'd gen
val map4 : ('a * 'b * 'c * 'd -> 'e) -> ('a gen * 'b gen * 'c gen * 'd gen) -> 'e gen

val flip : bool gen
val flip' : int * int -> bool gen

val list : bool gen -> 'a gen -> 'a list gen
val option : bool gen -> 'a gen -> 'a option gen
val vector : (int * (int -> 'a) -> 'b) -> int gen * 'a gen -> 'b gen

val variant : (int, 'b) co
val arrow : ('a, 'b) co * 'b gen -> ('a -> 'b) gen
val cobool : (bool, 'b) co
val colist : ('a, 'b) co -> ('a list, 'b) co
val coopt : ('a, 'b) co -> ('a option, 'b) co

type stream
val start : rand -> stream
val limit : int -> 'a gen -> ('a, stream) reader

end

structure Base_Generator : BASE_GENERATOR =
struct

(* random number engine *)

type rand = real

val a = 16807.0
val m = 2147483647.0

fun nextrand seed =
  let
    val t = a * seed
  in
    t - m * real (floor (t / m))
  end

val new = nextrand o Time.toReal o Time.now

fun range (min, max) =
  if min > max then raise Domain (* TODO: raise its own error *)
  else fn r => (min + (floor (real (max - min + 1) * r / m)), nextrand r)

fun split r =
  let
    val r = r / a
    val r0 = real (floor r)
    val r1 = r - r0
  in
    (nextrand r0, nextrand r1)
  end

(* generators *)

type 'a gen = rand -> 'a * rand
type ('a, 'b) reader = 'b -> ('a * 'b) option

fun lift obj r = (obj, r)

local (* Isabelle does not use vectors? *)
  fun explode ((freq, gen), acc) =
    List.tabulate (freq, fn _ => gen) @ acc
in
  fun choose v r =
    let val (i, r) = range(0, Vector.length v - 1) r
    in Vector.sub (v, i) r end
  fun choose' v = choose (Vector.fromList (Vector.foldr explode [] v))
  fun select v = choose (Vector.map lift v)
end

fun chooseL l = choose (Vector.fromList l)
fun chooseL' l = choose' (Vector.fromList l)
fun selectL l = select (Vector.fromList l)

fun zip (g1, g2) = g1 #-> (fn x1 => g2 #-> (fn x2 => pair (x1, x2)))

fun zip3 (g1, g2, g3) =
  zip (g1, zip (g2, g3)) #-> (fn (x1, (x2, x3)) => pair (x1, x2, x3))

fun zip4 (g1, g2, g3, g4) =
  zip (zip (g1, g2), zip (g3, g4)) #-> (fn ((x1, x2), (x3, x4)) => pair (x1, x2, x3, x4))

fun map f g = apfst f o g

fun map2 f = map f o zip
fun map3 f = map f o zip3
fun map4 f = map f o zip4

fun filter p gen r =
  let
    fun loop (x, r) = if p x then (x, r) else loop (gen r)
  in
    loop (gen r)
  end

val flip = selectL [true, false]
fun flip' (p, q) = chooseL' [(p, lift true), (q, lift false)]

fun list flip g r =
  case flip r of
      (true, r) => ([], r)
    | (false, r) =>
      let
        val (x,r) = g r
        val (xs,r) = list flip g r
      in (x::xs, r) end

fun option flip g r =
  case flip r of
    (true, r) => (NONE, r)
  | (false, r) => map SOME g r

fun vector tabulate (int, elem) r =
  let
    val (n, r) = int r
    val p = Unsynchronized.ref r
    fun g _ =
      let
        val (x,r) = elem(!p)
      in x before p := r end
  in
    (tabulate(n, g), !p)
  end

type stream = rand Unsynchronized.ref * int

fun start r = (Unsynchronized.ref r, 0)

fun limit max gen =
  let
    fun next (p, i) =
      if i >= max then NONE
      else
        let val (x, r) = gen(!p)
        in SOME(x, (p, i+1)) before p := r end
  in
    next
  end

type ('a, 'b) co = 'a -> 'b gen -> 'b gen

fun variant v g r =
  let
    fun nth (i, r) =
      let val (r1, r2) = split r
      in if i = 0 then r1 else nth (i-1, r2) end
  in
    g (nth (v, r))
  end

fun arrow (cogen, gen) r =
  let
    val (r1, r2) = split r
    fun g x = fst (cogen x gen r1)
  in (g, r2) end

fun cobool false = variant 0
  | cobool true = variant 1

fun colist _ [] = variant 0
  | colist co (x::xs) = variant 1 o co x o colist co xs

fun coopt _ NONE = variant 0
  | coopt co (SOME x) = variant 1 o co x

end

