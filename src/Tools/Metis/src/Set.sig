(* ========================================================================= *)
(* FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004 Joe Hurd, distributed under the MIT license            *)
(* ========================================================================= *)

signature Set =
sig

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type 'elt set

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

val empty : ('elt * 'elt -> order) -> 'elt set

val singleton : ('elt * 'elt -> order) -> 'elt -> 'elt set

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

val null : 'elt set -> bool

val size : 'elt set -> int

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

val peek : 'elt set -> 'elt -> 'elt option

val member : 'elt -> 'elt set -> bool

val pick : 'elt set -> 'elt  (* an arbitrary element *)

val nth : 'elt set -> int -> 'elt  (* in the range [0,size-1] *)

val random : 'elt set -> 'elt

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

val add : 'elt set -> 'elt -> 'elt set

val addList : 'elt set -> 'elt list -> 'elt set

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

val delete : 'elt set -> 'elt -> 'elt set  (* must be present *)

val remove : 'elt set -> 'elt -> 'elt set

val deletePick : 'elt set -> 'elt * 'elt set

val deleteNth : 'elt set -> int -> 'elt * 'elt set

val deleteRandom : 'elt set -> 'elt * 'elt set

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

val union : 'elt set -> 'elt set -> 'elt set

val unionList : 'elt set list -> 'elt set

val intersect : 'elt set -> 'elt set -> 'elt set

val intersectList : 'elt set list -> 'elt set

val difference : 'elt set -> 'elt set -> 'elt set

val symmetricDifference : 'elt set -> 'elt set -> 'elt set

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

val filter : ('elt -> bool) -> 'elt set -> 'elt set

val partition : ('elt -> bool) -> 'elt set -> 'elt set * 'elt set

val app : ('elt -> unit) -> 'elt set -> unit

val foldl : ('elt * 's -> 's) -> 's -> 'elt set -> 's

val foldr : ('elt * 's -> 's) -> 's -> 'elt set -> 's

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

val findl : ('elt -> bool) -> 'elt set -> 'elt option

val findr : ('elt -> bool) -> 'elt set -> 'elt option

val firstl : ('elt -> 'a option) -> 'elt set -> 'a option

val firstr : ('elt -> 'a option) -> 'elt set -> 'a option

val exists : ('elt -> bool) -> 'elt set -> bool

val all : ('elt -> bool) -> 'elt set -> bool

val count : ('elt -> bool) -> 'elt set -> int

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

val compare : 'elt set * 'elt set -> order

val equal : 'elt set -> 'elt set -> bool

val subset : 'elt set -> 'elt set -> bool

val disjoint : 'elt set -> 'elt set -> bool

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

val transform : ('elt -> 'a) -> 'elt set -> 'a list

val toList : 'elt set -> 'elt list

val fromList : ('elt * 'elt -> order) -> 'elt list -> 'elt set

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

type ('elt,'a) map = ('elt,'a) Map.map

val mapPartial : ('elt -> 'a option) -> 'elt set -> ('elt,'a) map

val map : ('elt -> 'a) -> 'elt set -> ('elt,'a) map

val domain : ('elt,'a) map -> 'elt set

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

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
