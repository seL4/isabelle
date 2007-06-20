(* ========================================================================= *)
(* FINITE MAPS WITH A FIXED KEY TYPE                                         *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

functor KeyMap (Key : Ordered) :> KeyMap where type key = Key.t =
struct

(*isabelle open Metis;*)

type key = Key.t;

(* ------------------------------------------------------------------------- *)
(* Finite maps                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a map = (Key.t,'a) Map.map;

fun new () = Map.new Key.compare;

val null = Map.null;

val size = Map.size;

fun singleton key_value = Map.singleton Key.compare key_value;

val inDomain = Map.inDomain;

val peek = Map.peek;

val insert = Map.insert;

val insertList = Map.insertList;

val get = Map.get;

(* Both union and intersect prefer keys in the second map *)

val union = Map.union;

val intersect = Map.intersect;

val delete = Map.delete;

val difference = Map.difference;

val subsetDomain = Map.subsetDomain;

val equalDomain = Map.equalDomain;

val mapPartial = Map.mapPartial;

val filter = Map.filter;

val map = Map.map;

val app = Map.app;

val transform = Map.transform;

val foldl = Map.foldl;

val foldr = Map.foldr;

val findl = Map.findl;

val findr = Map.findr;

val firstl = Map.firstl;

val firstr = Map.firstr;

val exists = Map.exists;

val all = Map.all;

val domain = Map.domain;

val toList = Map.toList;

fun fromList l = Map.fromList Key.compare l;

val compare = Map.compare;

val equal = Map.equal;

val random = Map.random;

val toString = Map.toString;

(* ------------------------------------------------------------------------- *)
(* Iterators over maps                                                       *)
(* ------------------------------------------------------------------------- *)

type 'a iterator = (Key.t,'a) Map.iterator;

val mkIterator = Map.mkIterator;

val mkRevIterator = Map.mkRevIterator;

val readIterator = Map.readIterator;

val advanceIterator = Map.advanceIterator;

end

(*isabelle structure Metis = struct open Metis*)

structure IntMap =
KeyMap (IntOrdered);

structure StringMap =
KeyMap (StringOrdered);

(*isabelle end;*)
