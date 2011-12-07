(* ========================================================================= *)
(* FINITE MAPS WITH A FIXED KEY TYPE                                         *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

signature KeyMap =
sig

(* ------------------------------------------------------------------------- *)
(* A type of map keys.                                                       *)
(* ------------------------------------------------------------------------- *)

type key

val compareKey : key * key -> order

val equalKey : key -> key -> bool

(* ------------------------------------------------------------------------- *)
(* A type of finite maps.                                                    *)
(* ------------------------------------------------------------------------- *)

type 'a map

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

val new : unit -> 'a map

val singleton : key * 'a -> 'a map

(* ------------------------------------------------------------------------- *)
(* Map size.                                                                 *)
(* ------------------------------------------------------------------------- *)

val null : 'a map -> bool

val size : 'a map -> int

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

val peekKey : 'a map -> key -> (key * 'a) option

val peek : 'a map -> key -> 'a option

val get : 'a map -> key -> 'a  (* raises Error *)

val pick : 'a map -> key * 'a  (* an arbitrary key/value pair *)

val nth : 'a map -> int -> key * 'a  (* in the range [0,size-1] *)

val random : 'a map -> key * 'a

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

val insert : 'a map -> key * 'a -> 'a map

val insertList : 'a map -> (key * 'a) list -> 'a map

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

val delete : 'a map -> key -> 'a map  (* must be present *)

val remove : 'a map -> key -> 'a map

val deletePick : 'a map -> (key * 'a) * 'a map

val deleteNth : 'a map -> int -> (key * 'a) * 'a map

val deleteRandom : 'a map -> (key * 'a) * 'a map

(* ------------------------------------------------------------------------- *)
(* Joining (all join operations prefer keys in the second map).              *)
(* ------------------------------------------------------------------------- *)

val merge :
    {first : key * 'a -> 'c option,
     second : key * 'b -> 'c option,
     both : (key * 'a) * (key * 'b) -> 'c option} ->
    'a map -> 'b map -> 'c map

val union :
    ((key * 'a) * (key * 'a) -> 'a option) ->
    'a map -> 'a map -> 'a map

val intersect :
    ((key * 'a) * (key * 'b) -> 'c option) ->
    'a map -> 'b map -> 'c map

(* ------------------------------------------------------------------------- *)
(* Set operations on the domain.                                             *)
(* ------------------------------------------------------------------------- *)

val inDomain : key -> 'a map -> bool

val unionDomain : 'a map -> 'a map -> 'a map

val unionListDomain : 'a map list -> 'a map

val intersectDomain : 'a map -> 'a map -> 'a map

val intersectListDomain : 'a map list -> 'a map

val differenceDomain : 'a map -> 'a map -> 'a map

val symmetricDifferenceDomain : 'a map -> 'a map -> 'a map

val equalDomain : 'a map -> 'a map -> bool

val subsetDomain : 'a map -> 'a map -> bool

val disjointDomain : 'a map -> 'a map -> bool

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

val mapPartial : (key * 'a -> 'b option) -> 'a map -> 'b map

val map : (key * 'a -> 'b) -> 'a map -> 'b map

val app : (key * 'a -> unit) -> 'a map -> unit

val transform : ('a -> 'b) -> 'a map -> 'b map

val filter : (key * 'a -> bool) -> 'a map -> 'a map

val partition :
    (key * 'a -> bool) -> 'a map -> 'a map * 'a map

val foldl : (key * 'a * 's -> 's) -> 's -> 'a map -> 's

val foldr : (key * 'a * 's -> 's) -> 's -> 'a map -> 's

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

val findl : (key * 'a -> bool) -> 'a map -> (key * 'a) option

val findr : (key * 'a -> bool) -> 'a map -> (key * 'a) option

val firstl : (key * 'a -> 'b option) -> 'a map -> 'b option

val firstr : (key * 'a -> 'b option) -> 'a map -> 'b option

val exists : (key * 'a -> bool) -> 'a map -> bool

val all : (key * 'a -> bool) -> 'a map -> bool

val count : (key * 'a -> bool) -> 'a map -> int

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

val compare : ('a * 'a -> order) -> 'a map * 'a map -> order

val equal : ('a -> 'a -> bool) -> 'a map -> 'a map -> bool

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

val keys : 'a map -> key list

val values : 'a map -> 'a list

val toList : 'a map -> (key * 'a) list

val fromList : (key * 'a) list -> 'a map

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val toString : 'a map -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over maps.                                                      *)
(* ------------------------------------------------------------------------- *)

type 'a iterator

val mkIterator : 'a map -> 'a iterator option

val mkRevIterator : 'a map -> 'a iterator option

val readIterator : 'a iterator -> key * 'a

val advanceIterator : 'a iterator -> 'a iterator option

end
