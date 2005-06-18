(*  Title:      Pure/General/ord_list.ML
    ID:         $Id$
    Author:     Makarius

Ordered lists without duplicates -- a light-weight representation of
finite sets.
*)

signature ORD_LIST =
sig
  val member: ('b * 'a -> order) -> 'a list -> 'b -> bool
  val insert: ('a * 'a -> order) -> 'a -> 'a list -> 'a list
  val remove: ('b * 'a -> order) -> 'b -> 'a list -> 'a list
  val union: ('a * 'a -> order) -> 'a list -> 'a list -> 'a list
  val inter: ('a * 'a -> order) -> 'a list -> 'a list -> 'a list
end;

structure OrdList: ORD_LIST =
struct

fun member ord list x =
  let
    fun memb [] = false
      | memb (y :: ys) =
          (case ord (x, y) of
            LESS => false
          | EQUAL => true
          | GREATER => memb ys);
  in memb list end;

exception SAME;

fun insert ord x list =
  let
    fun insrt [] = [x]
      | insrt (lst as y :: ys) =
          (case ord (x, y) of
            LESS => x :: lst
          | EQUAL => raise SAME
          | GREATER => y :: insrt ys);
  in insrt list handle SAME => list end;

fun remove ord x list =
  let
    fun rmove [] = raise SAME
      | rmove (lst as y :: ys) =
          (case ord (x, y) of
            LESS => raise SAME
          | EQUAL => ys
          | GREATER => y :: rmove ys);
  in rmove list handle SAME => list end;

nonfix union;
fun union _ xs [] = xs
  | union _ [] ys = ys
  | union ord (lst1 as x :: xs) (lst2 as y :: ys) =
      (case ord (x, y) of
        LESS => x :: union ord xs lst2
      | EQUAL => x :: union ord xs ys
      | GREATER => y :: union ord lst1 ys);

nonfix inter;
fun inter _ _ [] = []
  | inter _ [] _ = []
  | inter ord (lst1 as x :: xs) (lst2 as y :: ys) =
      (case ord (x, y) of
        LESS => inter ord xs lst2
      | EQUAL => x :: inter ord xs ys
      | GREATER => inter ord lst1 ys);

end;
