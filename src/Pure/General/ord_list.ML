(*  Title:      Pure/General/ord_list.ML
    ID:         $Id$
    Author:     Makarius

Ordered lists without duplicates -- a light-weight representation of
finite sets, all operations take linear time and economize heap usage.
*)

signature ORD_LIST =
sig
  val member: ('b * 'a -> order) -> 'a list -> 'b -> bool
  val insert: ('a * 'a -> order) -> 'a -> 'a list -> 'a list
  val remove: ('b * 'a -> order) -> 'b -> 'a list -> 'a list
  val union: ('a * 'a -> order) -> 'a list -> 'a list -> 'a list
  val inter: ('b * 'a -> order) -> 'b list -> 'a list -> 'a list
  val subtract: ('b * 'a -> order) -> 'b list -> 'a list -> 'a list
end;

structure OrdList: ORD_LIST =
struct

exception SAME;
fun handle_same f x = f x handle SAME => x;

fun member ord list x =
  let
    fun memb [] = false
      | memb (y :: ys) =
          (case ord (x, y) of
            LESS => false
          | EQUAL => true
          | GREATER => memb ys);
  in memb list end;

fun insert ord x list =
  let
    fun insrt [] = [x]
      | insrt (lst as y :: ys) =
          (case ord (x, y) of
            LESS => x :: lst
          | EQUAL => raise SAME
          | GREATER => y :: insrt ys);
  in handle_same insrt list end;

fun remove ord x list =
  let
    fun rmove [] = raise SAME
      | rmove (y :: ys) =
          (case ord (x, y) of
            LESS => raise SAME
          | EQUAL => ys
          | GREATER => y :: rmove ys);
  in handle_same rmove list end;

(*union: insert elements of first list into second list*)
nonfix union;
fun union ord list1 list2 =
  let
    fun unio [] _ = raise SAME
      | unio xs [] = xs
      | unio (lst1 as x :: xs) (lst2 as y :: ys) =
          (case ord (x, y) of
            LESS => x :: handle_same (unio xs) lst2
          | EQUAL => y :: unio xs ys
          | GREATER => y :: unio lst1 ys);
  in handle_same (unio list1) list2 end;

(*intersection: filter second list for elements present in first list*)
nonfix inter;
fun inter ord list1 list2 =
  let
    fun intr _ [] = raise SAME
      | intr [] _ = []
      | intr (lst1 as x :: xs) (lst2 as y :: ys) =
          (case ord (x, y) of
            LESS => intr xs lst2
          | EQUAL => y :: intr xs ys
          | GREATER => handle_same (intr lst1) ys);
  in handle_same (intr list1) list2 end;

(*subtraction: filter second list for elements NOT present in first list*)
fun subtract ord list1 list2 =
  let
    fun subtr [] _ = raise SAME
      | subtr _ [] = raise SAME
      | subtr (lst1 as x :: xs) (lst2 as y :: ys) =
          (case ord (x, y) of
            LESS => subtr xs lst2
          | EQUAL => handle_same (subtr xs) ys
          | GREATER => y :: subtr lst1 ys);
  in handle_same (subtr list1) list2 end;

end;
