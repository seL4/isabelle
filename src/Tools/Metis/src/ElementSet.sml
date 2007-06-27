(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

functor ElementSet (Key : Ordered) :> ElementSet where type element = Key.t =
struct

(*isabelle open Metis;*)

type element = Key.t;

(* ------------------------------------------------------------------------- *)
(* Finite sets                                                               *)
(* ------------------------------------------------------------------------- *)

type set = Key.t Set.set;

val empty = Set.empty Key.compare;

fun singleton key = Set.singleton Key.compare key;

val null = Set.null;

val size = Set.size;

val member = Set.member;

val add = Set.add;

val addList = Set.addList;

val delete = Set.delete;

val union = Set.union;

val unionList = Set.unionList;

val intersect = Set.intersect;

val intersectList = Set.intersectList;

val difference = Set.difference;

val symmetricDifference = Set.symmetricDifference;

val disjoint = Set.disjoint;

val subset = Set.subset;

val equal = Set.equal;

val filter = Set.filter;

val partition = Set.partition;

val count = Set.count;

val foldl = Set.foldl;

val foldr = Set.foldr;

val findl = Set.findl;

val findr = Set.findr;

val firstl = Set.firstl;

val firstr = Set.firstr;

val exists = Set.exists;

val all = Set.all;

val map = Set.map;

val transform = Set.transform;

val app = Set.app;

val toList = Set.toList;

fun fromList l = Set.fromList Key.compare l;

val pick = Set.pick;

val random = Set.random;

val deletePick = Set.deletePick;

val deleteRandom = Set.deleteRandom;

val compare = Set.compare;

val close = Set.close;

val toString = Set.toString;

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type iterator = Key.t Set.iterator;

val mkIterator = Set.mkIterator;

val mkRevIterator = Set.mkRevIterator;

val readIterator = Set.readIterator;

val advanceIterator = Set.advanceIterator;

end

(*isabelle structure Metis = struct open Metis;*)

structure IntSet =
ElementSet (IntOrdered);

structure StringSet =
ElementSet (StringOrdered);

(*isabelle end;*)
