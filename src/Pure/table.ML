(*  Title:      Pure/table.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic tables (lacking delete operation).  Implemented as 2-3 trees.
*)

signature TABLE_DATA =
sig
  type key
  val ord: key * key -> order
end;

signature TABLE =
sig
  type key
  type 'a table
  exception DUP of key
  exception DUPS of key list
  val empty: 'a table
  val is_empty: 'a table -> bool
  val dest: 'a table -> (key * 'a) list
  val lookup: 'a table * key -> 'a option
  val update: (key * 'a) * 'a table -> 'a table
  val update_new: (key * 'a) * 'a table -> 'a table                     (*exception DUP*)
  val make: (key * 'a) list -> 'a table                                 (*exception DUPS*)
  val extend: 'a table * (key * 'a) list -> 'a table                    (*exception DUPS*)
  val merge: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table       (*exception DUPS*)
  val lookup_multi: 'a list table * key -> 'a list
  val make_multi: (key * 'a) list -> 'a list table
  val dest_multi: 'a list table -> (key * 'a) list
  val map: ('a -> 'b) -> 'a table -> 'b table
end;

functor TableFun(Data: TABLE_DATA): TABLE =
struct


(* datatype table *)

type key = Data.key;

datatype 'a table =
  Empty |
  Branch2 of 'a table * (key * 'a) * 'a table |
  Branch3 of 'a table * (key * 'a) * 'a table * (key * 'a) * 'a table;

exception DUP of key;
exception DUPS of key list;


val empty = Empty;

fun is_empty Empty = true
  | is_empty _ = false;

fun dest Empty = []
  | dest (Branch2 (left, p, right)) = dest left @ [p] @ dest right
  | dest (Branch3 (left, p1, mid, p2, right)) =
      dest left @ [p1] @ dest mid @ [p2] @ dest right;


(* lookup *)

fun lookup (Empty, _) = None
  | lookup (Branch2 (left, (k, x), right), key) =
      (case Data.ord (key, k) of
        LESS => lookup (left, key)
      | EQUAL => Some x
      | GREATER => lookup (right, key))
  | lookup (Branch3 (left, (k1, x1), mid, (k2, x2), right), key) =
      (case Data.ord (key, k1) of
        LESS => lookup (left, key)
      | EQUAL => Some x1
      | GREATER =>
          (case Data.ord (key, k2) of
            LESS => lookup (mid, key)
          | EQUAL => Some x2
          | GREATER => lookup (right, key)));


(* update *)

fun compare (k1, _) (k2, _) = Data.ord (k1, k2);

datatype 'a growth =
  Stay of 'a table |
  Sprout of 'a table * (key * 'a) * 'a table;

fun insert pair Empty = Sprout (Empty, pair, Empty)
  | insert pair (Branch2 (left, p, right)) =
      (case compare pair p of
        LESS =>
          (case insert pair left of
            Stay left' => Stay (Branch2 (left', p, right))
          | Sprout (left1, q, left2) => Stay (Branch3 (left1, q, left2, p, right)))
      | EQUAL => Stay (Branch2 (left, pair, right))
      | GREATER =>
          (case insert pair right of
            Stay right' => Stay (Branch2 (left, p, right'))
          | Sprout (right1, q, right2) =>
              Stay (Branch3 (left, p, right1, q, right2))))
  | insert pair (Branch3 (left, p1, mid, p2, right)) =
      (case compare pair p1 of
        LESS =>
          (case insert pair left of
            Stay left' => Stay (Branch3 (left', p1, mid, p2, right))
          | Sprout (left1, q, left2) =>
              Sprout (Branch2 (left1, q, left2), p1, Branch2 (mid, p2, right)))
      | EQUAL => Stay (Branch3 (left, pair, mid, p2, right))
      | GREATER =>
          (case compare pair p2 of
            LESS =>
              (case insert pair mid of
                Stay mid' => Stay (Branch3 (left, p1, mid', p2, right))
              | Sprout (mid1, q, mid2) =>
                  Sprout (Branch2 (left, p1, mid1), q, Branch2 (mid2, p2, right)))
          | EQUAL => Stay (Branch3 (left, p1, mid, pair, right))
          | GREATER =>
              (case insert pair right of
                Stay right' => Stay (Branch3 (left, p1, mid, p2, right'))
              | Sprout (right1, q, right2) =>
                  Sprout (Branch2 (left, p1, mid), p2, Branch2 (right1, q, right2)))));

fun update (pair, tab) =
  (case insert pair tab of
    Stay tab => tab
  | Sprout br => Branch2 br);

fun update_new (pair as (key, _), tab) =
  (case lookup (tab, key) of
    None => update (pair, tab)
  | Some _ => raise DUP key);


(* make, extend, merge tables *)

fun add eq ((tab, dups), (key, x)) =
  (case lookup (tab, key) of
    None => (update ((key, x), tab), dups)
  | Some x' =>
      if eq (x, x') then (tab, dups)
      else (tab, dups @ [key]));

fun enter eq (tab, pairs) =
  (case foldl (add eq) ((tab, []), pairs) of
    (tab', []) => tab'
  | (_, dups) => raise DUPS dups);

fun extend tab_pairs = enter (K false) tab_pairs;
fun make pairs = extend (empty, pairs);
fun merge eq (tab1, tab2) = enter eq (tab1, dest tab2);


(* tables with multiple entries per key (preserving order) *)

fun lookup_multi tab_key = if_none (lookup tab_key) [];

fun cons_entry ((key, entry), tab) =
  update ((key, entry :: lookup_multi (tab, key)), tab);

fun make_multi pairs = foldr cons_entry (pairs, empty);

fun dest_multi tab =
  flat (map (fn (key, xs) => map (pair key) xs) (dest tab));


(* map *)

fun map _ Empty = Empty
  | map f (Branch2 (left, (k, x), right)) =
      Branch2 (map f left, (k, f x), map f right)
  | map f (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
      Branch3 (map f left, (k1, f x1), map f mid, (k2, f x2), map f right);


end;


(*tables indexed by strings*)
structure Symtab = TableFun(type key = string val ord = string_ord);

(* FIXME demo *)
structure IntTab = TableFun(type key = int val ord = int_ord);
val make = IntTab.make o map (rpair ());
fun dest tab = IntTab.dest tab |> map fst;
