(* ========================================================================= *)
(* FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Set :> Set =
struct

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('elt,'a) map = ('elt,'a) Map.map;

datatype 'elt set = Set of ('elt,unit) map;

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

fun dest (Set m) = m;

fun mapPartial f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => Map.mapPartial mf m
    end;

fun map f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => Map.map mf m
    end;

fun domain m = Set (Map.transform (fn _ => ()) m);

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

fun empty cmp = Set (Map.new cmp);

fun singleton cmp elt = Set (Map.singleton cmp (elt,()));

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun null (Set m) = Map.null m;

fun size (Set m) = Map.size m;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun peek (Set m) elt =
    case Map.peekKey m elt of
      SOME (elt,()) => SOME elt
    | NONE => NONE;

fun member elt (Set m) = Map.inDomain elt m;

fun pick (Set m) =
    let
      val (elt,_) = Map.pick m
    in
      elt
    end;

fun nth (Set m) n =
    let
      val (elt,_) = Map.nth m n
    in
      elt
    end;

fun random (Set m) =
    let
      val (elt,_) = Map.random m
    in
      elt
    end;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

fun add (Set m) elt =
    let
      val m = Map.insert m (elt,())
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
      val m = Map.delete m elt
    in
      Set m
    end;

fun remove (Set m) elt =
    let
      val m = Map.remove m elt
    in
      Set m
    end;

fun deletePick (Set m) =
    let
      val ((elt,()),m) = Map.deletePick m
    in
      (elt, Set m)
    end;

fun deleteNth (Set m) n =
    let
      val ((elt,()),m) = Map.deleteNth m n
    in
      (elt, Set m)
    end;

fun deleteRandom (Set m) =
    let
      val ((elt,()),m) = Map.deleteRandom m
    in
      (elt, Set m)
    end;

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

fun union (Set m1) (Set m2) = Set (Map.unionDomain m1 m2);

fun unionList sets =
    let
      val ms = List.map dest sets
    in
      Set (Map.unionListDomain ms)
    end;

fun intersect (Set m1) (Set m2) = Set (Map.intersectDomain m1 m2);

fun intersectList sets =
    let
      val ms = List.map dest sets
    in
      Set (Map.intersectListDomain ms)
    end;

fun difference (Set m1) (Set m2) =
    Set (Map.differenceDomain m1 m2);

fun symmetricDifference (Set m1) (Set m2) =
    Set (Map.symmetricDifferenceDomain m1 m2);

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

fun filter pred =
    let
      fun mpred (elt,()) = pred elt
    in
      fn Set m => Set (Map.filter mpred m)
    end;

fun partition pred =
    let
      fun mpred (elt,()) = pred elt
    in
      fn Set m =>
         let
           val (m1,m2) = Map.partition mpred m
         in
           (Set m1, Set m2)
         end
    end;

fun app f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => Map.app mf m
    end;

fun foldl f =
    let
      fun mf (elt,(),acc) = f (elt,acc)
    in
      fn acc => fn Set m => Map.foldl mf acc m
    end;

fun foldr f =
    let
      fun mf (elt,(),acc) = f (elt,acc)
    in
      fn acc => fn Set m => Map.foldr mf acc m
    end;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

fun findl p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m =>
         case Map.findl mp m of
           SOME (elt,()) => SOME elt
         | NONE => NONE
    end;

fun findr p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m =>
         case Map.findr mp m of
           SOME (elt,()) => SOME elt
         | NONE => NONE
    end;

fun firstl f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => Map.firstl mf m
    end;

fun firstr f =
    let
      fun mf (elt,()) = f elt
    in
      fn Set m => Map.firstr mf m
    end;

fun exists p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => Map.exists mp m
    end;

fun all p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => Map.all mp m
    end;

fun count p =
    let
      fun mp (elt,()) = p elt
    in
      fn Set m => Map.count mp m
    end;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

fun compareValue ((),()) = EQUAL;

fun equalValue () () = true;

fun compare (Set m1, Set m2) = Map.compare compareValue (m1,m2);

fun equal (Set m1) (Set m2) = Map.equal equalValue m1 m2;

fun subset (Set m1) (Set m2) = Map.subsetDomain m1 m2;

fun disjoint (Set m1) (Set m2) = Map.disjointDomain m1 m2;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

fun transform f =
    let
      fun inc (x,l) = f x :: l
    in
      foldr inc []
    end;

fun toList (Set m) = Map.keys m;

fun fromList cmp elts = addList (empty cmp) elts;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun toString set =
    "{" ^ (if null set then "" else Int.toString (size set)) ^ "}";

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type 'elt iterator = ('elt,unit) Map.iterator;

fun mkIterator (Set m) = Map.mkIterator m;

fun mkRevIterator (Set m) = Map.mkRevIterator m;

fun readIterator iter =
    let
      val (elt,()) = Map.readIterator iter
    in
      elt
    end;

fun advanceIterator iter = Map.advanceIterator iter;

end
