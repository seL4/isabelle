structure FloatArith = 
struct

type float = IntInf.int * IntInf.int 

val izero = IntInf.fromInt 0
fun imul a b = IntInf.* (a,b)
fun isub a b = IntInf.- (a,b)
fun iadd a b = IntInf.+ (a,b)

val floatzero = (izero, izero)

fun positive_part (a,b) = 
    (if IntInf.< (a,izero) then izero else a, b)

fun negative_part (a,b) = 
    (if IntInf.< (a,izero) then a else izero, b)

fun is_negative (a,b) = 
    if IntInf.< (a, izero) then true else false

fun is_positive (a,b) = 
    if IntInf.< (izero, a) then true else false

fun is_zero (a,b) = 
    if a = izero then true else false

fun ipow2 a = IntInf.pow ((IntInf.fromInt 2), IntInf.toInt a)

fun add (a1, b1) (a2, b2) = 
    if IntInf.< (b1, b2) then
	(iadd a1 (imul a2 (ipow2 (isub b2 b1))), b1)
    else
	(iadd (imul a1 (ipow2 (isub b1 b2))) a2, b2)

fun sub (a1, b1) (a2, b2) = 
    if IntInf.< (b1, b2) then
	(isub a1 (imul a2 (ipow2 (isub b2 b1))), b1)
    else
	(isub (imul a1 (ipow2 (isub b1 b2))) a2, b2)

fun neg (a, b) = (IntInf.~ a, b)

fun is_equal a b = is_zero (sub a b)

fun is_less a b = is_negative (sub a b)

fun max a b = if is_less a b then b else a

fun min a b = if is_less a b then a else b

fun abs a = if is_negative a then neg a else a

fun mul (a1, b1) (a2, b2) = (imul a1 a2, iadd b1 b2)

end;
