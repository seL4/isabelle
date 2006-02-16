signature SCANNER_SEQ =
sig
    type 'a seq
    
    val pull : 'a seq -> ('a * 'a seq) option 
end

signature EXTENDED_SCANNER_SEQ =
sig

  include SCANNER_SEQ

  val null : 'a seq -> bool
  val length : 'a seq -> int
  val take_at_most : 'a seq -> int -> 'a list

end

functor ExtendScannerSeq (structure Seq : SCANNER_SEQ) : EXTENDED_SCANNER_SEQ =
struct
  
type 'a seq = 'a Seq.seq

val pull = Seq.pull

fun null s = is_none (pull s)

fun take_at_most s n = 
    if n <= 0 then [] else
    case pull s of 
	NONE => []
      | SOME (x,s') => x::(take_at_most s' (n-1))

fun length' s n = 
    case pull s of
	NONE => n
      | SOME (_, s') => length' s' (n+1)

fun length s = length' s 0
		
end  

signature VECTOR_SCANNER_SEQ = 
sig
    include EXTENDED_SCANNER_SEQ

    val fromString : string -> string seq
    val fromVector : 'a Vector.vector -> 'a seq
end

structure VectorScannerSeq :> VECTOR_SCANNER_SEQ =
struct
  
structure Incubator : SCANNER_SEQ =
struct

type 'a seq = 'a Vector.vector * int * int
fun pull (v, len, i) = if i >= len then NONE else SOME (Vector.sub (v, i), (v, len, i+1))

end

structure Extended = ExtendScannerSeq (structure Seq = Incubator)

open Extended

fun fromVector v = (v, Vector.length v, 0)
fun vector_from_string s = Vector.tabulate (String.size s, fn i => String.str (String.sub (s, i)))
fun fromString s = fromVector (vector_from_string s)

end

signature LIST_SCANNER_SEQ =
sig
    include EXTENDED_SCANNER_SEQ
    
    val fromString : string -> string seq
    val fromList : 'a list -> 'a seq
end

structure ListScannerSeq :> LIST_SCANNER_SEQ =
struct
     
structure Incubator : SCANNER_SEQ =
struct

type 'a seq = 'a list
fun pull [] = NONE
  | pull (x::xs) = SOME (x, xs)

end

structure Extended = ExtendScannerSeq (structure Seq = Incubator)

open Extended

val fromList = I
val fromString = Symbol.explode

end
