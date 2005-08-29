(*  Title:      Pure/General/table.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Generic tables.  Efficient purely functional implementation using
balanced 2-3 trees.
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
  exception UNDEF of key
  val empty: 'a table
  val is_empty: 'a table -> bool
  val map: ('a -> 'b) -> 'a table -> 'b table
  val map': (key -> 'a -> 'b) -> 'a table -> 'b table
  val fold: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val foldl: ('a * (key * 'b) -> 'a) -> 'a * 'b table -> 'a
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val min_key: 'a table -> key option
  val max_key: 'a table -> key option
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val forall: (key * 'a -> bool) -> 'a table -> bool
  val defined: 'a table -> key -> bool
  val lookup: 'a table * key -> 'a option
  val update: (key * 'a) * 'a table -> 'a table
  val update_new: (key * 'a) * 'a table -> 'a table                    (*exception DUP*)
  val default: key * 'a -> 'a table -> 'a table
  val map_entry: key -> ('a -> 'a) -> 'a table -> 'a table
  val make: (key * 'a) list -> 'a table                                (*exception DUPS*)
  val extend: 'a table * (key * 'a) list -> 'a table                   (*exception DUPS*)
  val join: (key -> 'a * 'a -> 'a option) ->
    'a table * 'a table -> 'a table                                    (*exception DUPS*)
  val merge: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table      (*exception DUPS*)
  val delete: key -> 'a table -> 'a table                              (*exception UNDEF*)
  val delete_safe: key -> 'a table -> 'a table
  val member: ('b * 'a -> bool) -> 'a table -> key * 'b -> bool
  val insert: ('a * 'a -> bool) -> key * 'a -> 'a table -> 'a table    (*exception DUP*)
  val remove: ('b * 'a -> bool) -> key * 'b -> 'a table -> 'a table
  val lookup_multi: 'a list table * key -> 'a list
  val update_multi: (key * 'a) * 'a list table -> 'a list table
  val remove_multi: ('b * 'a -> bool) -> key * 'b -> 'a list table -> 'a list table
  val make_multi: (key * 'a) list -> 'a list table
  val dest_multi: 'a list table -> (key * 'a) list
  val merge_multi: ('a * 'a -> bool) ->
    'a list table * 'a list table -> 'a list table                     (*exception DUPS*)
  val merge_multi': ('a * 'a -> bool) ->
    'a list table * 'a list table -> 'a list table                     (*exception DUPS*)
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

fun map_table f =
  let
    fun map Empty = Empty
      | map (Branch2 (left, (k, x), right)) =
          Branch2 (map left, (k, f k x), map right)
      | map (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          Branch3 (map left, (k1, f k1 x1), map mid, (k2, f k2 x2), map right);
  in map end;

fun fold_table f =
  let
    fun fold Empty x = x
      | fold (Branch2 (left, p, right)) x =
          fold right (f p (fold left x))
      | fold (Branch3 (left, p1, mid, p2, right)) x =
          fold right (f p2 (fold mid (f p1 (fold left x))));
  in fold end;

fun dest tab = rev (fold_table cons tab []);
fun keys tab = rev (fold_table (cons o #1) tab []);

local exception TRUE in

fun exists pred tab =
  (fold_table (fn p => fn () => if pred p then raise TRUE else ()) tab (); false)
    handle TRUE => true;

fun forall pred = not o exists (not o pred);

end;

fun min_key Empty = NONE
  | min_key (Branch2 (Empty, (k, _), _)) = SOME k
  | min_key (Branch3 (Empty, (k, _), _, _, _)) = SOME k
  | min_key (Branch2 (left, _, _)) = min_key left
  | min_key (Branch3 (left, _, _, _, _)) = min_key left;

fun max_key Empty = NONE
  | max_key (Branch2 (_, (k, _), Empty)) = SOME k
  | max_key (Branch3 (_, _, _, (k, _), Empty)) = SOME k
  | max_key (Branch2 (_, _, right)) = max_key right
  | max_key (Branch3 (_, _, _, _, right)) = max_key right;


(* lookup *)

fun lookup (Empty, _) = NONE
  | lookup (Branch2 (left, (k, x), right), key) =
      (case Key.ord (key, k) of
        LESS => lookup (left, key)
      | EQUAL => SOME x
      | GREATER => lookup (right, key))
  | lookup (Branch3 (left, (k1, x1), mid, (k2, x2), right), key) =
      (case Key.ord (key, k1) of
        LESS => lookup (left, key)
      | EQUAL => SOME x1
      | GREATER =>
          (case Key.ord (key, k2) of
            LESS => lookup (mid, key)
          | EQUAL => SOME x2
          | GREATER => lookup (right, key)));

fun defined tab key = is_some (lookup (tab, key));


(* updates *)

datatype 'a growth =
  Stay of 'a table |
  Sprout of 'a table * (key * 'a) * 'a table;

exception SAME;

fun modify key f tab =
  let
    fun modfy Empty = Sprout (Empty, (key, f NONE), Empty)
      | modfy (Branch2 (left, p as (k, x), right)) =
          (case Key.ord (key, k) of
            LESS =>
              (case modfy left of
                Stay left' => Stay (Branch2 (left', p, right))
              | Sprout (left1, q, left2) => Stay (Branch3 (left1, q, left2, p, right)))
          | EQUAL => Stay (Branch2 (left, (k, f (SOME x)), right))
          | GREATER =>
              (case modfy right of
                Stay right' => Stay (Branch2 (left, p, right'))
              | Sprout (right1, q, right2) =>
                  Stay (Branch3 (left, p, right1, q, right2))))
      | modfy (Branch3 (left, p1 as (k1, x1), mid, p2 as (k2, x2), right)) =
          (case Key.ord (key, k1) of
            LESS =>
              (case modfy left of
                Stay left' => Stay (Branch3 (left', p1, mid, p2, right))
              | Sprout (left1, q, left2) =>
                  Sprout (Branch2 (left1, q, left2), p1, Branch2 (mid, p2, right)))
          | EQUAL => Stay (Branch3 (left, (k1, f (SOME x1)), mid, p2, right))
          | GREATER =>
              (case Key.ord (key, k2) of
                LESS =>
                  (case modfy mid of
                    Stay mid' => Stay (Branch3 (left, p1, mid', p2, right))
                  | Sprout (mid1, q, mid2) =>
                      Sprout (Branch2 (left, p1, mid1), q, Branch2 (mid2, p2, right)))
              | EQUAL => Stay (Branch3 (left, p1, mid, (k2, f (SOME x2)), right))
              | GREATER =>
                  (case modfy right of
                    Stay right' => Stay (Branch3 (left, p1, mid, p2, right'))
                  | Sprout (right1, q, right2) =>
                      Sprout (Branch2 (left, p1, mid), p2, Branch2 (right1, q, right2)))));

  in
    (case modfy tab of
      Stay tab' => tab'
    | Sprout br => Branch2 br)
    handle SAME => tab
  end;

fun update ((key, x), tab) = modify key (fn _ => x) tab;
fun update_new ((key, x), tab) = modify key (fn NONE => x | SOME _ => raise DUP key) tab;
fun default (p as (key, x)) tab = if defined tab key then tab else update (p, tab)
fun map_entry key f = modify key (fn NONE => raise SAME | SOME x => f x);


(* extend and make *)

fun extend (table, args) =
  let
    fun add (key, x) (tab, dups) =
      if defined tab key then (tab, key :: dups)
      else (update ((key, x), tab), dups);
  in
    (case fold add args (table, []) of
      (table', []) => table'
    | (_, dups) => raise DUPS (rev dups))
  end;

fun make pairs = extend (empty, pairs);


(* delete *)

exception UNDEF of key;

local

fun compare NONE (k2, _) = LESS
  | compare (SOME k1) (k2, _) = Key.ord (k1, k2);

fun if_eq EQUAL x y = x
  | if_eq _ x y = y;

fun del (SOME k) Empty = raise UNDEF k
  | del NONE (Branch2 (Empty, p, Empty)) = (p, (true, Empty))
  | del NONE (Branch3 (Empty, p, Empty, q, Empty)) =
      (p, (false, Branch2 (Empty, q, Empty)))
  | del k (Branch2 (Empty, p, Empty)) = (case compare k p of
      EQUAL => (p, (true, Empty)) | _ => raise UNDEF (the k))
  | del k (Branch3 (Empty, p, Empty, q, Empty)) = (case compare k p of
      EQUAL => (p, (false, Branch2 (Empty, q, Empty)))
    | _ => (case compare k q of
        EQUAL => (q, (false, Branch2 (Empty, p, Empty)))
      | _ => raise UNDEF (the k)))
  | del k (Branch2 (l, p, r)) = (case compare k p of
      LESS => (case del k l of
        (p', (false, l')) => (p', (false, Branch2 (l', p, r)))
      | (p', (true, l')) => (p', case r of
          Branch2 (rl, rp, rr) =>
            (true, Branch3 (l', p, rl, rp, rr))
        | Branch3 (rl, rp, rm, rq, rr) => (false, Branch2
            (Branch2 (l', p, rl), rp, Branch2 (rm, rq, rr)))))
    | ord => (case del (if_eq ord NONE k) r of
        (p', (false, r')) => (p', (false, Branch2 (l, if_eq ord p' p, r')))
      | (p', (true, r')) => (p', case l of
          Branch2 (ll, lp, lr) =>
            (true, Branch3 (ll, lp, lr, if_eq ord p' p, r'))
        | Branch3 (ll, lp, lm, lq, lr) => (false, Branch2
            (Branch2 (ll, lp, lm), lq, Branch2 (lr, if_eq ord p' p, r'))))))
  | del k (Branch3 (l, p, m, q, r)) = (case compare k q of
      LESS => (case compare k p of
        LESS => (case del k l of
          (p', (false, l')) => (p', (false, Branch3 (l', p, m, q, r)))
        | (p', (true, l')) => (p', (false, case (m, r) of
            (Branch2 (ml, mp, mr), Branch2 _) =>
              Branch2 (Branch3 (l', p, ml, mp, mr), q, r)
          | (Branch3 (ml, mp, mm, mq, mr), _) =>
              Branch3 (Branch2 (l', p, ml), mp, Branch2 (mm, mq, mr), q, r)
          | (Branch2 (ml, mp, mr), Branch3 (rl, rp, rm, rq, rr)) =>
              Branch3 (Branch2 (l', p, ml), mp, Branch2 (mr, q, rl), rp,
                Branch2 (rm, rq, rr)))))
      | ord => (case del (if_eq ord NONE k) m of
          (p', (false, m')) =>
            (p', (false, Branch3 (l, if_eq ord p' p, m', q, r)))
        | (p', (true, m')) => (p', (false, case (l, r) of
            (Branch2 (ll, lp, lr), Branch2 _) =>
              Branch2 (Branch3 (ll, lp, lr, if_eq ord p' p, m'), q, r)
          | (Branch3 (ll, lp, lm, lq, lr), _) =>
              Branch3 (Branch2 (ll, lp, lm), lq,
                Branch2 (lr, if_eq ord p' p, m'), q, r)
          | (_, Branch3 (rl, rp, rm, rq, rr)) =>
              Branch3 (l, if_eq ord p' p, Branch2 (m', q, rl), rp,
                Branch2 (rm, rq, rr))))))
    | ord => (case del (if_eq ord NONE k) r of
        (q', (false, r')) =>
          (q', (false, Branch3 (l, p, m, if_eq ord q' q, r')))
      | (q', (true, r')) => (q', (false, case (l, m) of
          (Branch2 _, Branch2 (ml, mp, mr)) =>
            Branch2 (l, p, Branch3 (ml, mp, mr, if_eq ord q' q, r'))
        | (_, Branch3 (ml, mp, mm, mq, mr)) =>
            Branch3 (l, p, Branch2 (ml, mp, mm), mq,
              Branch2 (mr, if_eq ord q' q, r'))
        | (Branch3 (ll, lp, lm, lq, lr), Branch2 (ml, mp, mr)) =>
            Branch3 (Branch2 (ll, lp, lm), lq, Branch2 (lr, p, ml), mp,
              Branch2 (mr, if_eq ord q' q, r'))))));

in

fun delete key tab = snd (snd (del (SOME key) tab));
fun delete_safe key tab = delete key tab handle UNDEF _ => tab;

end;


(* member, insert and remove *)

fun member eq tab (key, x) =
  (case lookup (tab, key) of
    NONE => false
  | SOME y => eq (x, y));

fun insert eq (key, x) =
  modify key (fn NONE => x | SOME y => if eq (x, y) then raise SAME else raise DUP key);

fun remove eq (key, x) tab =
  (case lookup (tab, key) of
    NONE => tab
  | SOME y => if eq (x, y) then delete key tab else tab);


(* join and merge *)

fun join f (table1, table2) =
  let
    fun add (key, x) (tab, dups) =
      (case lookup (tab, key) of
        NONE => (update ((key, x), tab), dups)
      | SOME y =>
          (case f key (y, x) of
            SOME z => (update ((key, z), tab), dups)
          | NONE => (tab, key :: dups)));
  in
    (case fold_table add table2 (table1, []) of
      (table', []) => table'
    | (_, dups) => raise DUPS (rev dups))
  end;

fun merge eq tabs = join (fn _ => fn (y, x) => if eq (y, x) then SOME y else NONE) tabs;


(* tables with multiple entries per key *)

fun lookup_multi arg = if_none (lookup arg) [];

fun update_multi ((key, x), tab) = modify key (fn NONE => [x] | SOME xs => x :: xs) tab;

fun remove_multi eq (key, x) tab =
  map_entry key (fn xs => (case Library.remove eq x xs of [] => raise UNDEF key | ys => ys)) tab
  handle UNDEF _ => delete key tab;

fun make_multi args = foldr update_multi empty args;
fun dest_multi tab = List.concat (map (fn (key, xs) => map (pair key) xs) (dest tab));
fun merge_multi eq = join (fn _ => fn (xs, xs') => SOME (gen_merge_lists eq xs xs'));
fun merge_multi' eq = join (fn _ => fn (xs, xs') => SOME (gen_merge_lists' eq xs xs'));


(*final declarations of this structure!*)
fun map f = map_table (K f);
val map' = map_table;
val fold = fold_table;
fun foldl f (x, tab) = fold (fn p => fn x' => f (x', p)) tab x;

end;

structure Inttab = TableFun(type key = int val ord = int_ord);
structure Symtab = TableFun(type key = string val ord = fast_string_ord);
