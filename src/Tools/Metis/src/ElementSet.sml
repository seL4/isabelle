(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

functor ElementSet (
  KM : KeyMap
) :> ElementSet
where type element = KM.key
and type 'a map = 'a KM.map =
struct

(* ------------------------------------------------------------------------- *)
(* A type of set elements.                                                   *)
(* ------------------------------------------------------------------------- *)

type element = KM.key;

val compareElement = KM.compareKey;

val equalElement = KM.equalKey;

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type 'a map = 'a KM.map;

datatype set = Set of unit map;

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

fun dest (Set m) = m;

fun mapPartial f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.mapPartial mf m
    end;

fun map f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.map mf m
    end;

fun domain m = Set (KM.transform (fn _ => ()) m);

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

val empty = Set (KM.new ());

fun singleton elt = Set (KM.singleton (elt,()));

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun null (Set m) = KM.null m;

fun size (Set m) = KM.size m;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun peek (Set m) elt =
    case KM.peekKey m elt of
      SOME (elt,()) => SOME elt
    | NONE => NONE;

fun member elt (Set m) = KM.inDomain elt m;

fun pick (Set m) =
    let
      val (elt,_) = KM.pick m
    in
      elt
    end;

fun nth (Set m) n =
    let
      val (elt,_) = KM.nth m n
    in
      elt
    end;

fun random (Set m) =
    let
      val (elt,_) = KM.random m
    in
      elt
    end;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

fun add (Set m) elt =
    let
      val m = KM.insert m (elt,())
    in
      Set m
    end;

local
  fun uncurriedAdd (elt,set) = add set elt;
in
  fun addList set = List.foldl uncurriedAdd set;
end;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun delete (Set m) elt =
    let
      val m = KM.delete m elt
    in
      Set m
    end;

fun remove (Set m) elt =
    let
      val m = KM.remove m elt
    in
      Set m
    end;

fun deletePick (Set m) =
    let
      val ((elt,()),m) = KM.deletePick m
    in
      (elt, Set m)
    end;

fun deleteNth (Set m) n =
    let
      val ((elt,()),m) = KM.deleteNth m n
    in
      (elt, Set m)
    end;

fun deleteRandom (Set m) =
    let
      val ((elt,()),m) = KM.deleteRandom m
    in
      (elt, Set m)
    end;

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

fun union (Set m1) (Set m2) = Set (KM.unionDomain m1 m2);

fun unionList sets =
    let
      val ms = List.map dest sets
    in
      Set (KM.unionListDomain ms)
    end;

fun intersect (Set m1) (Set m2) = Set (KM.intersectDomain m1 m2);

fun intersectList sets =
    let
      val ms = List.map dest sets
    in
      Set (KM.intersectListDomain ms)
    end;

fun difference (Set m1) (Set m2) =
    Set (KM.differenceDomain m1 m2);

fun symmetricDifference (Set m1) (Set m2) =
    Set (KM.symmetricDifferenceDomain m1 m2);

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

fun filter pred =
    let
      fun mpred (elt,()) = pred elt
    in
      fn Set m => Set (KM.filter mpred m)
    end;

fun partition pred =
    let
      fun mpred (elt,()) = pred elt
    in
      fn Set m =>
         let
           val (m1,m2) = KM.partition mpred m
         in
           (Set m1, Set m2)
         end
    end;

fun app f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.app mf m
    end;

fun foldl f =
    let
      fun mf (elt,(),acc) = f (elt,acc)
    in
      fn acc => fn Set m => KM.foldl mf acc m
    end;

fun foldr f =
    let
      fun mf (elt,(),acc) = f (elt,acc)
    in
      fn acc => fn Set m => KM.foldr mf acc m
    end;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

fun findl p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m =>
         case KM.findl mp m of
           SOME (elt,()) => SOME elt
         | NONE => NONE
    end;

fun findr p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m =>
         case KM.findr mp m of
           SOME (elt,()) => SOME elt
         | NONE => NONE
    end;

fun firstl f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.firstl mf m
    end;

fun firstr f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => KM.firstr mf m
    end;

fun exists p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => KM.exists mp m
    end;

fun all p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => KM.all mp m
    end;

fun count p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => KM.count mp m
    end;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

fun compareValue ((),()) = EQUAL;

fun equalValue () () = true;

fun compare (Set m1, Set m2) = KM.compare compareValue (m1,m2);

fun equal (Set m1) (Set m2) = KM.equal equalValue m1 m2;

fun subset (Set m1) (Set m2) = KM.subsetDomain m1 m2;

fun disjoint (Set m1) (Set m2) = KM.disjointDomain m1 m2;

(* ------------------------------------------------------------------------- *)
(* Closing under an operation.                                               *)
(* ------------------------------------------------------------------------- *)

fun closedAdd f =
    let
      fun adds acc set = foldl check acc set

      and check (elt,acc) =
          if member elt acc then acc
          else expand (add acc elt) elt

      and expand acc elt = adds acc (f elt)
    in
      adds
    end;

fun close f = closedAdd f empty;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

fun transform f =
    let
      fun inc (x,l) = f x :: l
    in
      foldr inc []
    end;

fun toList (Set m) = KM.keys m;

fun fromList elts = addList empty elts;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun toString set =
    "{" ^ (if null set then "" else Int.toString (size set)) ^ "}";

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type iterator = unit KM.iterator;

fun mkIterator (Set m) = KM.mkIterator m;

fun mkRevIterator (Set m) = KM.mkRevIterator m;

fun readIterator iter =
    let
      val (elt,()) = KM.readIterator iter
    in
      elt
    end;

fun advanceIterator iter = KM.advanceIterator iter;

end

structure IntSet =
ElementSet (IntMap);

structure IntPairSet =
ElementSet (IntPairMap);

structure StringSet =
ElementSet (StringMap);
