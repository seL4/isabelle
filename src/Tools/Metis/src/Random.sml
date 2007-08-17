(* Random -- Moscow ML library 1995-04-23, 1999-02-24 *)

structure Random :> Random =
struct

type generator = {seedref : real ref}

(* Generating random numbers.  Paulson, page 96 *)

val a = 16807.0 
val m = 2147483647.0 
fun nextrand seed = 
    let val t = a*seed 
    in t - m * real(floor(t/m)) end

fun newgenseed seed =
    {seedref = ref (nextrand seed)};

fun newgen () = newgenseed (Time.toReal (Time.now ()));

fun random {seedref} = CRITICAL (fn () => 
    (seedref := nextrand (! seedref); ! seedref / m));

fun randomlist (n, {seedref}) = CRITICAL (fn () =>
    let val seed0 = ! seedref
        fun h 0 seed res = (seedref := seed; res)
	  | h i seed res = h (i-1) (nextrand seed) (seed / m :: res)
    in h n seed0 [] end);

fun range (min, max) = 
    if min > max then raise Fail "Random.range: empty range" 
    else 
	fn {seedref} => CRITICAL (fn () =>
	(seedref := nextrand (! seedref); min + (floor(real(max-min) * ! seedref / m))));

fun rangelist (min, max) =
    if min > max then raise Fail "Random.rangelist: empty range" 
    else 
	fn (n, {seedref}) => CRITICAL (fn () => 
	let val seed0 = ! seedref
            fun h 0 seed res = (seedref := seed; res)
	      | h i seed res = h (i-1) (nextrand seed) 
		               (min + floor(real(max-min) * seed / m) :: res)
	in h n seed0 [] end)

end
