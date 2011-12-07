(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

signature ElementSet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of set elements.                                                   *)
(* ------------------------------------------------------------------------- *)

type element

val compareElement : element * element -> order

val equalElement : element -> element -> bool

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type set

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

val empty : set

val singleton : element -> set

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

val null : set -> bool

val size : set -> int

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

val peek : set -> element -> element option

val member : element -> set -> bool

val pick : set -> element  (* an arbitrary element *)

val nth : set -> int -> element  (* in the range [0,size-1] *)

val random : set -> element

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

val add : set -> element -> set

val addList : set -> element list -> set

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

val delete : set -> element -> set  (* must be present *)

val remove : set -> element -> set

val deletePick : set -> element * set

val deleteNth : set -> int -> element * set

val deleteRandom : set -> element * set

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

val union : set -> set -> set

val unionList : set list -> set

val intersect : set -> set -> set

val intersectList : set list -> set

val difference : set -> set -> set

val symmetricDifference : set -> set -> set

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

val filter : (element -> bool) -> set -> set

val partition : (element -> bool) -> set -> set * set

val app : (element -> unit) -> set -> unit

val foldl : (element * 's -> 's) -> 's -> set -> 's

val foldr : (element * 's -> 's) -> 's -> set -> 's

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

val findl : (element -> bool) -> set -> element option

val findr : (element -> bool) -> set -> element option

val firstl : (element -> 'a option) -> set -> 'a option

val firstr : (element -> 'a option) -> set -> 'a option

val exists : (element -> bool) -> set -> bool

val all : (element -> bool) -> set -> bool

val count : (element -> bool) -> set -> int

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

val compare : set * set -> order

val equal : set -> set -> bool

val subset : set -> set -> bool

val disjoint : set -> set -> bool

(* ------------------------------------------------------------------------- *)
(* Closing under an operation.                                               *)
(* ------------------------------------------------------------------------- *)

val closedAdd : (element -> set) -> set -> set -> set

val close : (element -> set) -> set -> set

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

val transform : (element -> 'a) -> set -> 'a list

val toList : set -> element list

val fromList : element list -> set

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

type 'a map

val mapPartial : (element -> 'a option) -> set -> 'a map

val map : (element -> 'a) -> set -> 'a map

val domain : 'a map -> set

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

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
