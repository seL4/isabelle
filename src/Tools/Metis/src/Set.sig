(* ========================================================================= *)
(* FINITE SETS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Set =
sig

(* ------------------------------------------------------------------------- *)
(* Finite sets                                                               *)
(* ------------------------------------------------------------------------- *)

type 'elt set

val comparison : 'elt set -> ('elt * 'elt -> order)

val empty : ('elt * 'elt -> order) -> 'elt set

val singleton : ('elt * 'elt -> order) -> 'elt -> 'elt set

val null : 'elt set -> bool

val size : 'elt set -> int

val member : 'elt -> 'elt set -> bool

val add : 'elt set -> 'elt -> 'elt set

val addList : 'elt set -> 'elt list -> 'elt set

val delete : 'elt set -> 'elt -> 'elt set  (* raises Error *)

(* Union and intersect prefer elements in the second set *)

val union : 'elt set -> 'elt set -> 'elt set

val unionList : 'elt set list -> 'elt set

val intersect : 'elt set -> 'elt set -> 'elt set

val intersectList : 'elt set list -> 'elt set

val difference : 'elt set -> 'elt set -> 'elt set

val symmetricDifference : 'elt set -> 'elt set -> 'elt set

val disjoint : 'elt set -> 'elt set -> bool

val subset : 'elt set -> 'elt set -> bool

val equal : 'elt set -> 'elt set -> bool

val filter : ('elt -> bool) -> 'elt set -> 'elt set

val partition : ('elt -> bool) -> 'elt set -> 'elt set * 'elt set

val count : ('elt -> bool) -> 'elt set -> int

val foldl : ('elt * 's -> 's) -> 's -> 'elt set -> 's

val foldr : ('elt * 's -> 's) -> 's -> 'elt set -> 's

val findl : ('elt -> bool) -> 'elt set -> 'elt option

val findr : ('elt -> bool) -> 'elt set -> 'elt option

val firstl : ('elt -> 'a option) -> 'elt set -> 'a option

val firstr : ('elt -> 'a option) -> 'elt set -> 'a option

val exists : ('elt -> bool) -> 'elt set -> bool

val all : ('elt -> bool) -> 'elt set -> bool

val map : ('elt -> 'a) -> 'elt set -> ('elt * 'a) list

val transform : ('elt -> 'a) -> 'elt set -> 'a list

val app : ('elt -> unit) -> 'elt set -> unit

val toList : 'elt set -> 'elt list

val fromList : ('elt * 'elt -> order) -> 'elt list -> 'elt set

val pick : 'elt set -> 'elt  (* raises Empty *)

val random : 'elt set -> 'elt  (* raises Empty *)

val deletePick : 'elt set -> 'elt * 'elt set  (* raises Empty *)

val deleteRandom : 'elt set -> 'elt * 'elt set  (* raises Empty *)

val compare : 'elt set * 'elt set -> order

val close : ('elt set -> 'elt set) -> 'elt set -> 'elt set

val toString : 'elt set -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type 'elt iterator

val mkIterator : 'elt set -> 'elt iterator option

val mkRevIterator : 'elt set -> 'elt iterator option

val readIterator : 'elt iterator -> 'elt

val advanceIterator : 'elt iterator -> 'elt iterator option

end
