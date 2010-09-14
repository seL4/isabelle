(* ========================================================================= *)
(* FINITE MAPS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

signature Map =
sig

(* ------------------------------------------------------------------------- *)
(* A type of finite maps.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('key,'a) map

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

val new : ('key * 'key -> order) -> ('key,'a) map

val singleton : ('key * 'key -> order) -> 'key * 'a -> ('key,'a) map

(* ------------------------------------------------------------------------- *)
(* Map size.                                                                 *)
(* ------------------------------------------------------------------------- *)

val null : ('key,'a) map -> bool

val size : ('key,'a) map -> int

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

val peekKey : ('key,'a) map -> 'key -> ('key * 'a) option

val peek : ('key,'a) map -> 'key -> 'a option

val get : ('key,'a) map -> 'key -> 'a  (* raises Error *)

val pick : ('key,'a) map -> 'key * 'a  (* an arbitrary key/value pair *)

val nth : ('key,'a) map -> int -> 'key * 'a  (* in the range [0,size-1] *)

val random : ('key,'a) map -> 'key * 'a

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

val insert : ('key,'a) map -> 'key * 'a -> ('key,'a) map

val insertList : ('key,'a) map -> ('key * 'a) list -> ('key,'a) map

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

val delete : ('key,'a) map -> 'key -> ('key,'a) map  (* must be present *)

val remove : ('key,'a) map -> 'key -> ('key,'a) map

val deletePick : ('key,'a) map -> ('key * 'a) * ('key,'a) map

val deleteNth : ('key,'a) map -> int -> ('key * 'a) * ('key,'a) map

val deleteRandom : ('key,'a) map -> ('key * 'a) * ('key,'a) map

(* ------------------------------------------------------------------------- *)
(* Joining (all join operations prefer keys in the second map).              *)
(* ------------------------------------------------------------------------- *)

val merge :
    {first : 'key * 'a -> 'c option,
     second : 'key * 'b -> 'c option,
     both : ('key * 'a) * ('key * 'b) -> 'c option} ->
    ('key,'a) map -> ('key,'b) map -> ('key,'c) map

val union :
    (('key * 'a) * ('key * 'a) -> 'a option) ->
    ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val intersect :
    (('key * 'a) * ('key * 'b) -> 'c option) ->
    ('key,'a) map -> ('key,'b) map -> ('key,'c) map

(* ------------------------------------------------------------------------- *)
(* Set operations on the domain.                                             *)
(* ------------------------------------------------------------------------- *)

val inDomain : 'key -> ('key,'a) map -> bool

val unionDomain : ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val unionListDomain : ('key,'a) map list -> ('key,'a) map

val intersectDomain : ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val intersectListDomain : ('key,'a) map list -> ('key,'a) map

val differenceDomain : ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val symmetricDifferenceDomain : ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val equalDomain : ('key,'a) map -> ('key,'a) map -> bool

val subsetDomain : ('key,'a) map -> ('key,'a) map -> bool

val disjointDomain : ('key,'a) map -> ('key,'a) map -> bool

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

val mapPartial : ('key * 'a -> 'b option) -> ('key,'a) map -> ('key,'b) map

val map : ('key * 'a -> 'b) -> ('key,'a) map -> ('key,'b) map

val app : ('key * 'a -> unit) -> ('key,'a) map -> unit

val transform : ('a -> 'b) -> ('key,'a) map -> ('key,'b) map

val filter : ('key * 'a -> bool) -> ('key,'a) map -> ('key,'a) map

val partition :
    ('key * 'a -> bool) -> ('key,'a) map -> ('key,'a) map * ('key,'a) map

val foldl : ('key * 'a * 's -> 's) -> 's -> ('key,'a) map -> 's

val foldr : ('key * 'a * 's -> 's) -> 's -> ('key,'a) map -> 's

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

val findl : ('key * 'a -> bool) -> ('key,'a) map -> ('key * 'a) option

val findr : ('key * 'a -> bool) -> ('key,'a) map -> ('key * 'a) option

val firstl : ('key * 'a -> 'b option) -> ('key,'a) map -> 'b option

val firstr : ('key * 'a -> 'b option) -> ('key,'a) map -> 'b option

val exists : ('key * 'a -> bool) -> ('key,'a) map -> bool

val all : ('key * 'a -> bool) -> ('key,'a) map -> bool

val count : ('key * 'a -> bool) -> ('key,'a) map -> int

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

val compare : ('a * 'a -> order) -> ('key,'a) map * ('key,'a) map -> order

val equal : ('a -> 'a -> bool) -> ('key,'a) map -> ('key,'a) map -> bool

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

val keys : ('key,'a) map -> 'key list

val values : ('key,'a) map -> 'a list

val toList : ('key,'a) map -> ('key * 'a) list

val fromList : ('key * 'key -> order) -> ('key * 'a) list -> ('key,'a) map

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val toString : ('key,'a) map -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over maps.                                                      *)
(* ------------------------------------------------------------------------- *)

type ('key,'a) iterator

val mkIterator : ('key,'a) map -> ('key,'a) iterator option

val mkRevIterator : ('key,'a) map -> ('key,'a) iterator option

val readIterator : ('key,'a) iterator -> 'key * 'a

val advanceIterator : ('key,'a) iterator -> ('key,'a) iterator option

end
