signature SUSP =
sig

type 'a susp

val force : 'a susp -> 'a
val delay : (unit -> 'a) -> 'a susp
val value : 'a -> 'a susp

end

structure Susp :> SUSP =
struct

datatype 'a suspVal
  = Value of 'a
  | Delay of unit -> 'a

type 'a susp = 'a suspVal ref

fun force (ref (Value v)) = v
  | force (r as ref (Delay f)) =
    let
	val v = f ()
    in
	r := Value v;
	v
    end

fun delay f = ref (Delay f)

fun value v = ref (Value v)

end
