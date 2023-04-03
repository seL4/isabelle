(*  Title:      Pure/General/table.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Generic tables.  Efficient purely functional implementation using
balanced 2-3 trees.
*)

signature KEY =
sig
  type key
  val ord: key ord
end;

signature TABLE =
sig
  structure Key: KEY
  type key
  type 'a table
  exception DUP of key
  exception SAME
  exception UNDEF of key
  val size: 'a table -> int
  val empty: 'a table
  val build: ('a table -> 'a table) -> 'a table
  val is_empty: 'a table -> bool
  val map: (key -> 'a -> 'b) -> 'a table -> 'b table
  val fold: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val fold_rev: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val min: 'a table -> (key * 'a) option
  val max: 'a table -> (key * 'a) option
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val forall: (key * 'a -> bool) -> 'a table -> bool
  val get_first: (key * 'a -> 'b option) -> 'a table -> 'b option
  val lookup_key: 'a table -> key -> (key * 'a) option
  val lookup: 'a table -> key -> 'a option
  val defined: 'a table -> key -> bool
  val update: key * 'a -> 'a table -> 'a table
  val update_new: key * 'a -> 'a table -> 'a table                     (*exception DUP*)
  val default: key * 'a -> 'a table -> 'a table
  val map_entry: key -> ('a -> 'a) (*exception SAME*) -> 'a table -> 'a table
  val map_default: key * 'a -> ('a -> 'a) -> 'a table -> 'a table
  val make: (key * 'a) list -> 'a table                                (*exception DUP*)
  val join: (key -> 'a * 'a -> 'a) (*exception SAME*) ->
    'a table * 'a table -> 'a table                                    (*exception DUP*)
  val merge: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table      (*exception DUP*)
  val delete: key -> 'a table -> 'a table                              (*exception UNDEF*)
  val delete_safe: key -> 'a table -> 'a table
  val member: ('b * 'a -> bool) -> 'a table -> key * 'b -> bool
  val insert: ('a * 'a -> bool) -> key * 'a -> 'a table -> 'a table    (*exception DUP*)
  val remove: ('b * 'a -> bool) -> key * 'b -> 'a table -> 'a table
  val lookup_list: 'a list table -> key -> 'a list
  val cons_list: key * 'a -> 'a list table -> 'a list table
  val insert_list: ('a * 'a -> bool) -> key * 'a -> 'a list table -> 'a list table
  val remove_list: ('b * 'a -> bool) -> key * 'b -> 'a list table -> 'a list table
  val update_list: ('a * 'a -> bool) -> key * 'a -> 'a list table -> 'a list table
  val make_list: (key * 'a) list -> 'a list table
  val dest_list: 'a list table -> (key * 'a) list
  val merge_list: ('a * 'a -> bool) -> 'a list table * 'a list table -> 'a list table
  type set = unit table
  val insert_set: key -> set -> set
  val remove_set: key -> set -> set
  val make_set: key list -> set
end;

functor Table(Key: KEY): TABLE =
struct

(* keys *)

structure Key = Key;
type key = Key.key;

exception DUP of key;


(* datatype *)

datatype 'a table =
  Empty |
  Leaf1 of key * 'a |
  Leaf2 of (key * 'a) * (key * 'a) |
  Leaf3 of (key * 'a) * (key * 'a) * (key * 'a) |
  Branch2 of 'a table * (key * 'a) * 'a table |
  Branch3 of 'a table * (key * 'a) * 'a table * (key * 'a) * 'a table;

(*literal copy from set.ML*)
fun make2 (Empty, e, Empty) = Leaf1 e
  | make2 (Branch2 (Empty, e1, Empty), e2, right) = make2 (Leaf1 e1, e2, right)
  | make2 (left, e1, Branch2 (Empty, e2, Empty)) = make2 (left, e1, Leaf1 e2)
  | make2 (Branch3 (Empty, e1, Empty, e2, Empty), e3, right) = make2 (Leaf2 (e1, e2), e3, right)
  | make2 (left, e1, Branch3 (Empty, e2, Empty, e3, Empty)) = make2 (left, e1, Leaf2 (e2, e3))
  | make2 (Leaf1 e1, e2, Empty) = Leaf2 (e1, e2)
  | make2 (Empty, e1, Leaf1 e2) = Leaf2 (e1, e2)
  | make2 (Leaf1 e1, e2, Leaf1 e3) = Leaf3 (e1, e2, e3)
  | make2 (Leaf2 (e1, e2), e3, Empty) = Leaf3 (e1, e2, e3)
  | make2 (Empty, e1, Leaf2 (e2, e3)) = Leaf3 (e1, e2, e3)
  | make2 arg = Branch2 arg;

(*literal copy from set.ML*)
fun make3 (Empty, e1, Empty, e2, Empty) = Leaf2 (e1, e2)
  | make3 (Branch2 (Empty, e1, Empty), e2, mid, e3, right) = make3 (Leaf1 e1, e2, mid, e3, right)
  | make3 (left, e1, Branch2 (Empty, e2, Empty), e3, right) = make3 (left, e1, Leaf1 e2, e3, right)
  | make3 (left, e1, mid, e2, Branch2 (Empty, e3, Empty)) = make3 (left, e1, mid, e2, Leaf1 e3)
  | make3 (Leaf1 e1, e2, Empty, e3, Empty) = Leaf3 (e1, e2, e3)
  | make3 (Empty, e1, Leaf1 e2, e3, Empty) = Leaf3 (e1, e2, e3)
  | make3 (Empty, e1, Empty, e2, Leaf1 e3) = Leaf3 (e1, e2, e3)
  | make3 arg = Branch3 arg;

(*literal copy from set.ML*)
fun unmake (Leaf1 e) = Branch2 (Empty, e, Empty)
  | unmake (Leaf2 (e1, e2)) = Branch3 (Empty, e1, Empty, e2, Empty)
  | unmake (Leaf3 (e1, e2, e3)) =
      Branch2 (Branch2 (Empty, e1, Empty), e2, Branch2 (Empty, e3, Empty))
  | unmake arg = arg;


(* size *)

local
  (*literal copy from set.ML*)
  fun count Empty n = n
    | count (Leaf1 _) n = n + 1
    | count (Leaf2 _) n = n + 2
    | count (Leaf3 _) n = n + 3
    | count (Branch2 (left, _, right)) n = count right (count left (n + 1))
    | count (Branch3 (left, _, mid, _, right)) n = count right (count mid (count left (n + 2)));
in
  fun size tab = Integer.build (count tab);
end;


(* empty *)

val empty = Empty;

fun build (f: 'a table -> 'a table) = f empty;

fun is_empty Empty = true
  | is_empty _ = false;


(* map and fold combinators *)

fun map_table f =
  let
    fun map Empty = Empty
      | map (Leaf1 (k, x)) = Leaf1 (k, f k x)
      | map (Leaf2 ((k1, x1), (k2, x2))) = Leaf2 ((k1, f k1 x1), (k2, f k2 x2))
      | map (Leaf3 ((k1, x1), (k2, x2), (k3, x3))) =
          Leaf3 ((k1, f k1 x1), (k2, f k2 x2), (k3, f k3 x3))
      | map (Branch2 (left, (k, x), right)) =
          Branch2 (map left, (k, f k x), map right)
      | map (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          Branch3 (map left, (k1, f k1 x1), map mid, (k2, f k2 x2), map right);
  in map end;

fun fold_table f =
  let
    fun fold Empty x = x
      | fold (Leaf1 e) x = f e x
      | fold (Leaf2 (e1, e2)) x = f e2 (f e1 x)
      | fold (Leaf3 (e1, e2, e3)) x = f e3 (f e2 (f e1 x))
      | fold (Branch2 (left, e, right)) x =
          fold right (f e (fold left x))
      | fold (Branch3 (left, e1, mid, e2, right)) x =
          fold right (f e2 (fold mid (f e1 (fold left x))));
  in fold end;

fun fold_rev_table f =
  let
    fun fold_rev Empty x = x
      | fold_rev (Leaf1 e) x = f e x
      | fold_rev (Leaf2 (e1, e2)) x = f e1 (f e2 x)
      | fold_rev (Leaf3 (e1, e2, e3)) x = f e1 (f e2 (f e3 x))
      | fold_rev (Branch2 (left, e, right)) x =
          fold_rev left (f e (fold_rev right x))
      | fold_rev (Branch3 (left, e1, mid, e2, right)) x =
          fold_rev left (f e1 (fold_rev mid (f e2 (fold_rev right x))));
  in fold_rev end;

fun dest tab = Library.build (fold_rev_table cons tab);
fun keys tab = Library.build (fold_rev_table (cons o #1) tab);


(* min/max entries *)

fun min Empty = NONE
  | min (Leaf1 e) = SOME e
  | min (Leaf2 (e, _)) = SOME e
  | min (Leaf3 (e, _, _)) = SOME e
  | min (Branch2 (Empty, e, _)) = SOME e
  | min (Branch3 (Empty, e, _, _, _)) = SOME e
  | min (Branch2 (left, _, _)) = min left
  | min (Branch3 (left, _, _, _, _)) = min left;

fun max Empty = NONE
  | max (Leaf1 e) = SOME e
  | max (Leaf2 (_, e)) = SOME e
  | max (Leaf3 (_, _, e)) = SOME e
  | max (Branch2 (_, e, Empty)) = SOME e
  | max (Branch3 (_, _, _, e, Empty)) = SOME e
  | max (Branch2 (_, _, right)) = max right
  | max (Branch3 (_, _, _, _, right)) = max right;


(* exists and forall *)

fun exists pred =
  let
    fun ex Empty = false
      | ex (Leaf1 e) = pred e
      | ex (Leaf2 (e1, e2)) = pred e1 orelse pred e2
      | ex (Leaf3 (e1, e2, e3)) = pred e1 orelse pred e2 orelse pred e3
      | ex (Branch2 (left, e, right)) =
          ex left orelse pred e orelse ex right
      | ex (Branch3 (left, e1, mid, e2, right)) =
          ex left orelse pred e1 orelse ex mid orelse pred e2 orelse ex right;
  in ex end;

fun forall pred = not o exists (not o pred);


(* get_first *)

fun get_first f =
  let
    fun get Empty = NONE
      | get (Leaf1 e) = f e
      | get (Leaf2 (e1, e2)) =
          (case f e1 of
            NONE => f e2
          | some => some)
      | get (Leaf3 (e1, e2, e3)) =
          (case f e1 of
            NONE =>
              (case f e2 of
                NONE => f e3
              | some => some)
          | some => some)
      | get (Branch2 (left, e, right)) =
          (case get left of
            NONE =>
              (case f e of
                NONE => get right
              | some => some)
          | some => some)
      | get (Branch3 (left, e1, mid, e2, right)) =
          (case get left of
            NONE =>
              (case f e1 of
                NONE =>
                  (case get mid of
                    NONE =>
                      (case f e2 of
                        NONE => get right
                      | some => some)
                  | some => some)
              | some => some)
          | some => some);
  in get end;


(* lookup *)

fun lookup tab key =
  let
    fun key_ord k = Key.ord (key, k);
    val key_eq = is_equal o key_ord;

    fun look Empty = NONE
      | look (Leaf1 (k, x)) =
          if key_eq k then SOME x else NONE
      | look (Leaf2 ((k1, x1), (k2, x2))) =
          (case key_ord k1 of
            LESS => NONE
          | EQUAL => SOME x1
          | GREATER => if key_eq k2 then SOME x2 else NONE)
      | look (Leaf3 ((k1, x1), (k2, x2), (k3, x3))) =
          (case key_ord k2 of
            LESS => if key_eq k1 then SOME x1 else NONE
          | EQUAL => SOME x2
          | GREATER => if key_eq k3 then SOME x3 else NONE)
      | look (Branch2 (left, (k, x), right)) =
          (case key_ord k of
            LESS => look left
          | EQUAL => SOME x
          | GREATER => look right)
      | look (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          (case key_ord k1 of
            LESS => look left
          | EQUAL => SOME x1
          | GREATER =>
              (case key_ord k2 of
                LESS => look mid
              | EQUAL => SOME x2
              | GREATER => look right));
  in look tab end;

fun lookup_key tab key =
  let
    fun key_ord k = Key.ord (key, k);
    val key_eq = is_equal o key_ord;

    fun look Empty = NONE
      | look (Leaf1 (k, x)) =
          if key_eq k then SOME (k, x) else NONE
      | look (Leaf2 ((k1, x1), (k2, x2))) =
          (case key_ord k1 of
            LESS => NONE
          | EQUAL => SOME (k1, x1)
          | GREATER => if key_eq k2 then SOME (k2, x2) else NONE)
      | look (Leaf3 ((k1, x1), (k2, x2), (k3, x3))) =
          (case key_ord k2 of
            LESS => if key_eq k1 then SOME (k1, x1) else NONE
          | EQUAL => SOME (k2, x2)
          | GREATER => if key_eq k3 then SOME (k3, x3) else NONE)
      | look (Branch2 (left, (k, x), right)) =
          (case key_ord k of
            LESS => look left
          | EQUAL => SOME (k, x)
          | GREATER => look right)
      | look (Branch3 (left, (k1, x1), mid, (k2, x2), right)) =
          (case key_ord k1 of
            LESS => look left
          | EQUAL => SOME (k1, x1)
          | GREATER =>
              (case key_ord k2 of
                LESS => look mid
              | EQUAL => SOME (k2, x2)
              | GREATER => look right));
  in look tab end;

fun defined tab key =
  let
    fun key_ord k = Key.ord (key, k);
    val key_eq = is_equal o key_ord;

    fun def Empty = false
      | def (Leaf1 (k, _)) = key_eq k
      | def (Leaf2 ((k1, _), (k2, _))) =
          (case key_ord k1 of
            LESS => false
          | EQUAL => true
          | GREATER => key_eq k2)
      | def (Leaf3 ((k1, _), (k2, _), (k3, _))) =
          (case key_ord k2 of
            LESS => key_eq k1
          | EQUAL => true
          | GREATER => key_eq k3)
      | def (Branch2 (left, (k, _), right)) =
          (case key_ord k of
            LESS => def left
          | EQUAL => true
          | GREATER => def right)
      | def (Branch3 (left, (k1, _), mid, (k2, _), right)) =
          (case key_ord k1 of
            LESS => def left
          | EQUAL => true
          | GREATER =>
              (case key_ord k2 of
                LESS => def mid
              | EQUAL => true
              | GREATER => def right));
  in def tab end;


(* modify *)

datatype 'a growth =
  Stay of 'a table |
  Sprout of 'a table * (key * 'a) * 'a table;

exception SAME;

fun modify key f tab =
  let
    fun key_ord k = Key.ord (key, k);

    fun modfy Empty = Sprout (Empty, (key, f NONE), Empty)
      | modfy (t as Leaf1 _) = modfy (unmake t)
      | modfy (t as Leaf2 _) = modfy (unmake t)
      | modfy (t as Leaf3 _) = modfy (unmake t)
      | modfy (Branch2 (left, p as (k, x), right)) =
          (case key_ord k of
            LESS =>
              (case modfy left of
                Stay left' => Stay (make2 (left', p, right))
              | Sprout (left1, q, left2) => Stay (make3 (left1, q, left2, p, right)))
          | EQUAL => Stay (make2 (left, (k, f (SOME x)), right))
          | GREATER =>
              (case modfy right of
                Stay right' => Stay (make2 (left, p, right'))
              | Sprout (right1, q, right2) =>
                  Stay (make3 (left, p, right1, q, right2))))
      | modfy (Branch3 (left, p1 as (k1, x1), mid, p2 as (k2, x2), right)) =
          (case key_ord k1 of
            LESS =>
              (case modfy left of
                Stay left' => Stay (make3 (left', p1, mid, p2, right))
              | Sprout (left1, q, left2) =>
                  Sprout (make2 (left1, q, left2), p1, make2 (mid, p2, right)))
          | EQUAL => Stay (make3 (left, (k1, f (SOME x1)), mid, p2, right))
          | GREATER =>
              (case key_ord k2 of
                LESS =>
                  (case modfy mid of
                    Stay mid' => Stay (make3 (left, p1, mid', p2, right))
                  | Sprout (mid1, q, mid2) =>
                      Sprout (make2 (left, p1, mid1), q, make2 (mid2, p2, right)))
              | EQUAL => Stay (make3 (left, p1, mid, (k2, f (SOME x2)), right))
              | GREATER =>
                  (case modfy right of
                    Stay right' => Stay (make3 (left, p1, mid, p2, right'))
                  | Sprout (right1, q, right2) =>
                      Sprout (make2 (left, p1, mid), p2, make2 (right1, q, right2)))));

  in
    (case modfy tab of
      Stay tab' => tab'
    | Sprout br => make2 br)
    handle SAME => tab
  end;

fun update (key, x) tab = modify key (fn _ => x) tab;
fun update_new (key, x) tab = modify key (fn NONE => x | SOME _ => raise DUP key) tab;
fun default (key, x) tab = modify key (fn NONE => x | SOME _ => raise SAME) tab;
fun map_entry key f = modify key (fn NONE => raise SAME | SOME x => f x);
fun map_default (key, x) f = modify key (fn NONE => f x | SOME y => f y);


(* delete *)

exception UNDEF of key;

local

fun compare NONE _ = LESS
  | compare (SOME k1) (k2, _) = Key.ord (k1, k2);

fun if_equal ord x y = if is_equal ord then x else y;

(*literal copy from set.ML*)
fun del (SOME k) Empty = raise UNDEF k
  | del NONE Empty = raise Match
  | del NONE (Leaf1 p) = (p, (true, Empty))
  | del NONE (Leaf2 (p, q)) = (p, (false, Leaf1 q))
  | del k (Leaf1 p) =
      (case compare k p of
        EQUAL => (p, (true, Empty))
      | _ => raise UNDEF (the k))
  | del k (Leaf2 (p, q)) =
      (case compare k p of
        EQUAL => (p, (false, Leaf1 q))
      | _ =>
        (case compare k q of
          EQUAL => (q, (false, Leaf1 p))
        | _ => raise UNDEF (the k)))
  | del k (Leaf3 (p, q, r)) = del k (Branch2 (Leaf1 p, q, Leaf1 r))
  | del k (Branch2 (l, p, r)) =
      (case compare k p of
        LESS =>
          (case del k l of
            (p', (false, l')) => (p', (false, make2 (l', p, r)))
          | (p', (true, l')) => (p', case unmake r of
              Branch2 (rl, rp, rr) =>
                (true, make3 (l', p, rl, rp, rr))
            | Branch3 (rl, rp, rm, rq, rr) => (false, make2
                (make2 (l', p, rl), rp, make2 (rm, rq, rr)))))
      | ord =>
          (case del (if_equal ord NONE k) r of
            (p', (false, r')) => (p', (false, make2 (l, if_equal ord p' p, r')))
          | (p', (true, r')) => (p', case unmake l of
              Branch2 (ll, lp, lr) =>
                (true, make3 (ll, lp, lr, if_equal ord p' p, r'))
            | Branch3 (ll, lp, lm, lq, lr) => (false, make2
                (make2 (ll, lp, lm), lq, make2 (lr, if_equal ord p' p, r'))))))
  | del k (Branch3 (l, p, m, q, r)) =
      (case compare k q of
        LESS =>
          (case compare k p of
            LESS =>
              (case del k l of
                (p', (false, l')) => (p', (false, make3 (l', p, m, q, r)))
              | (p', (true, l')) => (p', (false, case (unmake m, unmake r) of
                  (Branch2 (ml, mp, mr), Branch2 _) =>
                    make2 (make3 (l', p, ml, mp, mr), q, r)
                | (Branch3 (ml, mp, mm, mq, mr), _) =>
                    make3 (make2 (l', p, ml), mp, make2 (mm, mq, mr), q, r)
                | (Branch2 (ml, mp, mr), Branch3 (rl, rp, rm, rq, rr)) =>
                    make3 (make2 (l', p, ml), mp, make2 (mr, q, rl), rp,
                      make2 (rm, rq, rr)))))
          | ord =>
              (case del (if_equal ord NONE k) m of
                (p', (false, m')) =>
                  (p', (false, make3 (l, if_equal ord p' p, m', q, r)))
              | (p', (true, m')) => (p', (false, case (unmake l, unmake r) of
                  (Branch2 (ll, lp, lr), Branch2 _) =>
                    make2 (make3 (ll, lp, lr, if_equal ord p' p, m'), q, r)
                | (Branch3 (ll, lp, lm, lq, lr), _) =>
                    make3 (make2 (ll, lp, lm), lq,
                      make2 (lr, if_equal ord p' p, m'), q, r)
                | (_, Branch3 (rl, rp, rm, rq, rr)) =>
                    make3 (l, if_equal ord p' p, make2 (m', q, rl), rp,
                      make2 (rm, rq, rr))))))
      | ord =>
          (case del (if_equal ord NONE k) r of
            (q', (false, r')) =>
              (q', (false, make3 (l, p, m, if_equal ord q' q, r')))
          | (q', (true, r')) => (q', (false, case (unmake l, unmake m) of
              (Branch2 _, Branch2 (ml, mp, mr)) =>
                make2 (l, p, make3 (ml, mp, mr, if_equal ord q' q, r'))
            | (_, Branch3 (ml, mp, mm, mq, mr)) =>
                make3 (l, p, make2 (ml, mp, mm), mq,
                  make2 (mr, if_equal ord q' q, r'))
            | (Branch3 (ll, lp, lm, lq, lr), Branch2 (ml, mp, mr)) =>
                make3 (make2 (ll, lp, lm), lq, make2 (lr, p, ml), mp,
                  make2 (mr, if_equal ord q' q, r'))))));

in

fun delete key tab = snd (snd (del (SOME key) tab));
fun delete_safe key tab = if defined tab key then delete key tab else tab;

end;


(* membership operations *)

fun member eq tab (key, x) =
  (case lookup tab key of
    NONE => false
  | SOME y => eq (x, y));

fun insert eq (key, x) =
  modify key (fn NONE => x | SOME y => if eq (x, y) then raise SAME else raise DUP key);

fun remove eq (key, x) tab =
  (case lookup tab key of
    NONE => tab
  | SOME y => if eq (x, y) then delete key tab else tab);


(* simultaneous modifications *)

fun make entries = build (fold update_new entries);

fun join f (table1, table2) =
  let
    fun add (key, y) tab = modify key (fn NONE => y | SOME x => f key (x, y)) tab;
  in
    if pointer_eq (table1, table2) then table1
    else if is_empty table1 then table2
    else fold_table add table2 table1
  end;

fun merge eq = join (fn key => fn xy => if eq xy then raise SAME else raise DUP key);


(* list tables *)

fun lookup_list tab key = these (lookup tab key);

fun cons_list (key, x) tab = modify key (fn NONE => [x] | SOME xs => x :: xs) tab;

fun insert_list eq (key, x) =
  modify key (fn NONE => [x] | SOME xs => if Library.member eq xs x then raise SAME else x :: xs);

fun remove_list eq (key, x) tab =
  map_entry key (fn xs => (case Library.remove eq x xs of [] => raise UNDEF key | ys => ys)) tab
  handle UNDEF _ => delete key tab;

fun update_list eq (key, x) =
  modify key (fn NONE => [x] | SOME [] => [x] | SOME (xs as y :: _) =>
    if eq (x, y) then raise SAME else Library.update eq x xs);

fun make_list args = build (fold_rev cons_list args);
fun dest_list tab = maps (fn (key, xs) => map (pair key) xs) (dest tab);
fun merge_list eq = join (fn _ => Library.merge eq);


(* set operations *)

type set = unit table;

fun insert_set x = default (x, ());
fun remove_set x : set -> set = delete_safe x;
fun make_set xs = build (fold insert_set xs);


(* ML pretty-printing *)

val _ =
  ML_system_pp (fn depth => fn pretty => fn tab =>
    ML_Pretty.to_polyml
      (ML_Pretty.enum "," "{" "}"
        (ML_Pretty.pair
          (ML_Pretty.from_polyml o ML_system_pretty)
          (ML_Pretty.from_polyml o pretty))
        (dest tab, depth)));


(*final declarations of this structure!*)
val map = map_table;
val fold = fold_table;
val fold_rev = fold_rev_table;

end;

structure Inttab = Table(type key = int val ord = int_ord);
structure Symtab = Table(type key = string val ord = fast_string_ord);
structure Symreltab = Table(type key = string * string
  val ord = prod_ord fast_string_ord fast_string_ord);
