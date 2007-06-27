(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature ElementSet =
sig

type element

(* ------------------------------------------------------------------------- *)
(* Finite sets                                                               *)
(* ------------------------------------------------------------------------- *)

type set

val empty : set

val singleton : element -> set

val null : set -> bool

val size : set -> int

val member : element -> set -> bool

val add : set -> element -> set

val addList : set -> element list -> set

val delete : set -> element -> set  (* raises Error *)

(* Union and intersect prefer elements in the second set *)

val union : set -> set -> set

val unionList : set list -> set

val intersect : set -> set -> set

val intersectList : set list -> set

val difference : set -> set -> set

val symmetricDifference : set -> set -> set

val disjoint : set -> set -> bool

val subset : set -> set -> bool

val equal : set -> set -> bool

val filter : (element -> bool) -> set -> set

val partition : (element -> bool) -> set -> set * set

val count : (element -> bool) -> set -> int

val foldl : (element * 's -> 's) -> 's -> set -> 's

val foldr : (element * 's -> 's) -> 's -> set -> 's

val findl : (element -> bool) -> set -> element option

val findr : (element -> bool) -> set -> element option

val firstl : (element -> 'a option) -> set -> 'a option

val firstr : (element -> 'a option) -> set -> 'a option

val exists : (element -> bool) -> set -> bool

val all : (element -> bool) -> set -> bool

val map : (element -> 'a) -> set -> (element * 'a) list

val transform : (element -> 'a) -> set -> 'a list

val app : (element -> unit) -> set -> unit

val toList : set -> element list

val fromList : element list -> set

val pick : set -> element  (* raises Empty *)

val random : set -> element  (* raises Empty *)

val deletePick : set -> element * set  (* raises Empty *)

val deleteRandom : set -> element * set  (* raises Empty *)

val compare : set * set -> order

val close : (set -> set) -> set -> set

val toString : set -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type iterator

val mkIterator : set -> iterator option

val mkRevIterator : set -> iterator option

val readIterator : iterator -> element

val advanceIterator : iterator -> iterator option

end
