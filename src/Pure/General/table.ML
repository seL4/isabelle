(*  Title:      Pure/General/table.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic tables and tables indexed by strings.  Efficient purely
functional implementation using balanced 2-3 trees.  No delete
operation (may store options instead).
*)

signature KEY =
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
  val map: ('a -> 'b) -> 'a table -> 'b table
  val foldl: ('a * (key * 'b) -> 'a) -> 'a * 'b table -> 'a
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val min_key: 'a table -> key option
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val lookup: 'a table * key -> 'a option
  val update: (key * 'a) * 'a table -> 'a table
  val update_new: (key * 'a) * 'a table -> 'a table                    (*exception DUP*)
  val make: (key * 'a) list -> 'a table                                (*exception DUPS*)
  val extend: 'a table * (key * 'a) list -> 'a table                   (*exception DUPS*)
  val join: ('a * 'a -> 'a option) -> 'a table * 'a table -> 'a table  (*exception DUPS*)
  val merge: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table      (*exception DUPS*)
  val lookup_multi: 'a list table * key -> 'a list
  val update_multi: (key * 'a) * 'a list table -> 'a list table
  val make_multi: (key * 'a) list -> 'a list table
  val dest_multi: 'a list table -> (key * 'a) list
  val merge_multi: ('a * 'a -> bool) ->
    'a list table * 'a list table -> 'a list table    (*exception DUPS*)
  val merge_multi': ('a * 'a -> bool) ->
    'a list table * 'a list table -> 'a list table    (*exception DUPS*)
end;

functor TableFun(Key: KEY): TABLE =
struct


(* datatype table *)

type key = Key.key;

datatype 'a table =
  Empty |
  Branch2 of 'a table * (key * 'a) * 'a table |
  Branch3 of 'a table * (key * 'a) * 'a table * (key * 'a) * 'a table;

exception DUP of key;
exception DUPS of key list;


(* empty *)

val empty = Empty;

fun is_empty Empty = true
  | is_empty _ = false;


(* map and fold combinators *)

fun map_table _ Empty = Empty
  | map_table f (Branch2 (left, (k, x), right)) =
      Branch2 (map_table f left, (k, f x), map_table f right)
  | map_table f (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
      Branch3 (map_table f left, (k1, f x1), map_table f mid, (k2, f x2), map_table f right);

fun foldl_table _ (x, Empty) = x
  | foldl_table f (x, Branch2 (left, p, right)) =
      foldl_table f (f (foldl_table f (x, left), p), right)
  | foldl_table f (x, Branch3 (left, p1, mid, p2, right)) =
      foldl_table f (f (foldl_table f (f (foldl_table f (x, left), p1), mid), p2), right);

fun dest tab = rev (foldl_table (fn (rev_ps, p) => p :: rev_ps) ([], tab));
fun keys tab = rev (foldl_table (fn (rev_ks, (k, _)) => k :: rev_ks) ([], tab));
fun exists P tab = foldl_table (fn (false, e) => P e | (b, _) => b) (false, tab);

fun min_key Empty = None
  | min_key (Branch2 (left, (k, _), _)) = Some (if_none (min_key left) k)
  | min_key (Branch3 (left, (k, _), _, _, _)) = Some (if_none (min_key left) k);


(* lookup *)

fun lookup (Empty, _) = None
  | lookup (Branch2 (left, (k, x), right), key) =
      (case Key.ord (key, k) of
        LESS => lookup (left, key)
      | EQUAL => Some x
      | GREATER => lookup (right, key))
  | lookup (Branch3 (left, (k1, x1), mid, (k2, x2), right), key) =
      (case Key.ord (key, k1) of
        LESS => lookup (left, key)
      | EQUAL => Some x1
      | GREATER =>
          (case Key.ord (key, k2) of
            LESS => lookup (mid, key)
          | EQUAL => Some x2
          | GREATER => lookup (right, key)));


(* update *)

fun compare (k1, _) (k2, _) = Key.ord (k1, k2);

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
  if is_none (lookup (tab, key)) then update (pair, tab)
  else raise DUP key;


(* extend and make *)

fun extend (table, pairs) =
  let
    fun add ((tab, dups), (key, x)) =
      (case lookup (tab, key) of
        None => (update ((key, x), tab), dups)
      | _ => (tab, key :: dups));
  in
    (case foldl add ((table, []), pairs) of
      (table', []) => table'
    | (_, dups) => raise DUPS (rev dups))
  end;

fun make pairs = extend (empty, pairs);


(* join and merge *)

fun join f (table1, table2) =
  let
    fun add ((tab, dups), (key, x)) =
      (case lookup (tab, key) of
        None => (update ((key, x), tab), dups)
      | Some y =>
          (case f (y, x) of
            Some z => (update ((key, z), tab), dups)
          | None => (tab, key :: dups)));
  in
    (case foldl_table add ((table1, []), table2) of
      (table', []) => table'
    | (_, dups) => raise DUPS (rev dups))
  end;

fun merge eq tabs = join (fn (y, x) => if eq (y, x) then Some y else None) tabs;


(* tables with multiple entries per key (preserving order) *)

fun lookup_multi tab_key = if_none (lookup tab_key) [];
fun update_multi ((key, x), tab) = update ((key, x :: lookup_multi (tab, key)), tab);

fun make_multi pairs = foldr update_multi (pairs, empty);
fun dest_multi tab = flat (map (fn (key, xs) => map (Library.pair key) xs) (dest tab));
fun merge_multi eq tabs = join (fn (xs, xs') => Some (gen_merge_lists eq xs xs')) tabs;
fun merge_multi' eq tabs = join (fn (xs, xs') => Some (gen_merge_lists' eq xs xs')) tabs;


(*final declarations of this structure!*)
val map = map_table;
val foldl = foldl_table;

end;


(*tables indexed by strings*)
structure Symtab = TableFun(type key = string val ord = string_ord);
