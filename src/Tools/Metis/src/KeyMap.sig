(* ========================================================================= *)
(* FINITE MAPS WITH A FIXED KEY TYPE                                         *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature KeyMap =
sig

type key

(* ------------------------------------------------------------------------- *)
(* Finite maps                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a map

val new : unit -> 'a map

val null : 'a map -> bool

val size : 'a map -> int

val singleton : key * 'a -> 'a map

val inDomain : key -> 'a map -> bool

val peek : 'a map -> key -> 'a option

val insert : 'a map -> key * 'a -> 'a map

val insertList : 'a map -> (key * 'a) list -> 'a map

val get : 'a map -> key -> 'a  (* raises Error *)

(* Union and intersect prefer keys in the second map *)

val union : ('a * 'a -> 'a option) -> 'a map -> 'a map -> 'a map

val intersect : ('a * 'a -> 'a option) -> 'a map -> 'a map -> 'a map

val delete : 'a map -> key -> 'a map  (* raises Error *)

val difference : 'a map -> 'a map -> 'a map

val subsetDomain : 'a map -> 'a map -> bool

val equalDomain : 'a map -> 'a map -> bool

val mapPartial : (key * 'a -> 'b option) -> 'a map -> 'b map

val filter : (key * 'a -> bool) -> 'a map -> 'a map

val map : (key * 'a -> 'b) -> 'a map -> 'b map

val app : (key * 'a -> unit) -> 'a map -> unit

val transform : ('a -> 'b) -> 'a map -> 'b map

val foldl : (key * 'a * 's -> 's) -> 's -> 'a map -> 's

val foldr : (key * 'a * 's -> 's) -> 's -> 'a map -> 's

val findl : (key * 'a -> bool) -> 'a map -> (key * 'a) option

val findr : (key * 'a -> bool) -> 'a map -> (key * 'a) option

val firstl : (key * 'a -> 'b option) -> 'a map -> 'b option

val firstr : (key * 'a -> 'b option) -> 'a map -> 'b option

val exists : (key * 'a -> bool) -> 'a map -> bool

val all : (key * 'a -> bool) -> 'a map -> bool

val domain : 'a map -> key list

val toList : 'a map -> (key * 'a) list

val fromList : (key * 'a) list -> 'a map

val compare : ('a * 'a -> order) -> 'a map * 'a map -> order

val equal : ('a -> 'a -> bool) -> 'a map -> 'a map -> bool

val random : 'a map -> key * 'a  (* raises Empty *)

val toString : 'a map -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over maps                                                       *)
(* ------------------------------------------------------------------------- *)

type 'a iterator

val mkIterator : 'a map -> 'a iterator option

val mkRevIterator : 'a map -> 'a iterator option

val readIterator : 'a iterator -> key * 'a

val advanceIterator : 'a iterator -> 'a iterator option

end
