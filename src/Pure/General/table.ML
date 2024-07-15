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
  val make_distinct: (key * 'a) list -> 'a table
  val make: (key * 'a) list -> 'a table                                (*exception DUP*)
  val join: (key -> 'a * 'a -> 'a) (*exception SAME*) ->
    'a table * 'a table -> 'a table                                    (*exception DUP*)
  val merge: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table      (*exception DUP*)
  val joins: (key -> 'a * 'a -> 'a) (*exception SAME*) ->
    'a table list -> 'a table                                          (*exception DUP*)
  val merges: ('a * 'a -> bool) -> 'a table list -> 'a table           (*exception DUP*)
  val delete: key -> 'a table -> 'a table                              (*exception UNDEF*)
  val delete_safe: key -> 'a table -> 'a table
  val member: ('b * 'a -> bool) -> 'a table -> key * 'b -> bool
  val insert: ('a * 'a -> bool) -> key * 'a -> 'a table -> 'a table    (*exception DUP*)
  val remove: ('b * 'a -> bool) -> key * 'b -> 'a table -> 'a table
  val lookup_list: 'a list table -> key -> 'a list
  val cons_list: key * 'a -> 'a list table -> 'a list table
  val insert_list: ('a * 'a -> bool) -> key * 'a -> 'a list table -> 'a list table
  val update_list: ('a * 'a -> bool) -> key * 'a -> 'a list table -> 'a list table
  val remove_list: ('b * 'a -> bool) -> key * 'b -> 'a list table -> 'a list table
  val make_list: (key * 'a) list -> 'a list table
  val dest_list: 'a list table -> (key * 'a) list
  val merge_list: ('a * 'a -> bool) -> 'a list table * 'a list table -> 'a list table
  type set = unit table
  val insert_set: key -> set -> set
  val remove_set: key -> set -> set
  val make_set: key list -> set
  type 'a cache_ops = {apply: key -> 'a, reset: unit -> unit}
  val unsynchronized_cache: (key -> 'a) -> 'a cache_ops
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
  Branch3 of 'a table * (key * 'a) * 'a table * (key * 'a) * 'a table |
  Size of int * 'a table;

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

fun make3 (Empty, e1, Empty, e2, Empty) = Leaf2 (e1, e2)
  | make3 (Branch2 (Empty, e1, Empty), e2, mid, e3, right) = make3 (Leaf1 e1, e2, mid, e3, right)
  | make3 (left, e1, Branch2 (Empty, e2, Empty), e3, right) = make3 (left, e1, Leaf1 e2, e3, right)
  | make3 (left, e1, mid, e2, Branch2 (Empty, e3, Empty)) = make3 (left, e1, mid, e2, Leaf1 e3)
  | make3 (Leaf1 e1, e2, Empty, e3, Empty) = Leaf3 (e1, e2, e3)
  | make3 (Empty, e1, Leaf1 e2, e3, Empty) = Leaf3 (e1, e2, e3)
  | make3 (Empty, e1, Empty, e2, Leaf1 e3) = Leaf3 (e1, e2, e3)
  | make3 arg = Branch3 arg;

fun unmake (Leaf1 e) = Branch2 (Empty, e, Empty)
  | unmake (Leaf2 (e1, e2)) = Branch3 (Empty, e1, Empty, e2, Empty)
  | unmake (Leaf3 (e1, e2, e3)) = Branch2 (Branch2 (Empty, e1, Empty), e2, Branch2 (Empty, e3, Empty))
  | unmake (Size (_, arg)) = arg
  | unmake arg = arg;


(* size *)

(*literal copy from set.ML*)
local
  fun count Empty n = n
    | count (Leaf1 _) n = n + 1
    | count (Leaf2 _) n = n + 2
    | count (Leaf3 _) n = n + 3
    | count (Branch2 (left, _, right)) n = count right (count left (n + 1))
    | count (Branch3 (left, _, mid, _, right)) n = count right (count mid (count left (n + 2)))
    | count (Size (m, _)) n = m + n;

  fun box (Branch2 _) = 1
    | box (Branch3 _) = 1
    | box _ = 0;

  fun bound arg b =
    if b > 0 then
      (case arg of
        Branch2 (left, _, right) =>
          bound right (bound left (b - box left - box right))
      | Branch3 (left, _, mid, _, right) =>
          bound right (bound mid (bound left (b - box left - box mid - box right)))
      | _ => b)
    else b;
in
  fun size arg = count arg 0;
  fun make_size m arg = if bound arg 3 <= 0 then Size (m, arg) else arg;
end;


(* empty *)

val empty = Empty;

fun build (f: 'a table -> 'a table) = f empty;

(*literal copy from set.ML*)
fun is_empty Empty = true
  | is_empty (Size (_, arg)) = is_empty arg
  | is_empty _ = false;


(* map and fold combinators *)

fun map_table f =
  let
    fun apply (k, x) = (k, f k x);

    fun map Empty = Empty
      | map (Leaf1 e) = Leaf1 (apply e)
      | map (Leaf2 (e1, e2)) = Leaf2 (apply e1, apply e2)
      | map (Leaf3 (e1, e2, e3)) = Leaf3 (apply e1, apply e2, apply e3)
      | map (Branch2 (left, e, right)) =
          Branch2 (map left, apply e, map right)
      | map (Branch3 (left, e1, mid, e2, right)) =
          Branch3 (map left, apply e1, map mid, apply e2, map right)
      | map (Size (m, arg)) = Size (m, map arg);
  in map end;

fun fold_table f =
  let
    fun fold Empty a = a
      | fold (Leaf1 e) a = f e a
      | fold (Leaf2 (e1, e2)) a = f e2 (f e1 a)
      | fold (Leaf3 (e1, e2, e3)) a = f e3 (f e2 (f e1 a))
      | fold (Branch2 (left, e, right)) a =
          fold right (f e (fold left a))
      | fold (Branch3 (left, e1, mid, e2, right)) a =
          fold right (f e2 (fold mid (f e1 (fold left a))))
      | fold (Size (_, arg)) a = fold arg a;
  in fold end;

fun fold_rev_table f =
  let
    fun fold_rev Empty a = a
      | fold_rev (Leaf1 e) a = f e a
      | fold_rev (Leaf2 (e1, e2)) a = f e1 (f e2 a)
      | fold_rev (Leaf3 (e1, e2, e3)) a = f e1 (f e2 (f e3 a))
      | fold_rev (Branch2 (left, e, right)) a =
          fold_rev left (f e (fold_rev right a))
      | fold_rev (Branch3 (left, e1, mid, e2, right)) a =
          fold_rev left (f e1 (fold_rev mid (f e2 (fold_rev right a))))
      | fold_rev (Size (_, arg)) a = fold_rev arg a;
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
  | min (Branch3 (left, _, _, _, _)) = min left
  | min (Size (_, arg)) = min arg;

fun max Empty = NONE
  | max (Leaf1 e) = SOME e
  | max (Leaf2 (_, e)) = SOME e
  | max (Leaf3 (_, _, e)) = SOME e
  | max (Branch2 (_, e, Empty)) = SOME e
  | max (Branch3 (_, _, _, e, Empty)) = SOME e
  | max (Branch2 (_, _, right)) = max right
  | max (Branch3 (_, _, _, _, right)) = max right
  | max (Size (_, arg)) = max arg;


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
          ex left orelse pred e1 orelse ex mid orelse pred e2 orelse ex right
      | ex (Size (_, arg)) = ex arg;
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
          | some => some)
      | get (Size (_, arg)) = get arg;
  in get end;


(* retrieve *)

fun retrieve {result, no_result} tab (key: key) =
  let
    fun compare (k, _) = Key.ord (key, k)
    fun result_equal e = if is_equal (compare e) then result e else no_result;

    fun find Empty = no_result
      | find (Leaf1 e) = result_equal e
      | find (Leaf2 (e1, e2)) =
          (case compare e1 of
            LESS => no_result
          | EQUAL => result e1
          | GREATER => result_equal e2)
      | find (Leaf3 (e1, e2, e3)) =
          (case compare e2 of
            LESS => result_equal e1
          | EQUAL => result e2
          | GREATER => result_equal e3)
      | find (Branch2 (left, e, right)) =
          (case compare e of
            LESS => find left
          | EQUAL => result e
          | GREATER => find right)
      | find (Branch3 (left, e1, mid, e2, right)) =
          (case compare e1 of
            LESS => find left
          | EQUAL => result e1
          | GREATER =>
              (case compare e2 of
                LESS => find mid
              | EQUAL => result e2
              | GREATER => find right))
      | find (Size (_, arg)) = find arg;
  in find tab end;

fun lookup tab key = retrieve {result = SOME o #2, no_result = NONE} tab key;
fun lookup_key tab key = retrieve {result = SOME, no_result = NONE} tab key;
fun defined tab key = retrieve {result = K true, no_result = false} tab key;


(* modify *)

datatype 'a growth =
  Stay of 'a table |
  Sprout of 'a table * (key * 'a) * 'a table;

exception SAME;

fun modify key f tab =
  let
    fun compare (k, _) = Key.ord (key, k)

    val inc = Unsynchronized.ref 0;
    fun insert (k: key) = (k, f NONE) before ignore (Unsynchronized.inc inc);
    fun update (k: key, x) = (k, f (SOME x));

    fun modfy Empty = Sprout (Empty, (insert key), Empty)
      | modfy (t as Leaf1 _) = modfy (unmake t)
      | modfy (t as Leaf2 _) = modfy (unmake t)
      | modfy (t as Leaf3 _) = modfy (unmake t)
      | modfy (Branch2 (left, e, right)) =
          (case compare e of
            LESS =>
              (case modfy left of
                Stay left' => Stay (make2 (left', e, right))
              | Sprout (left1, e', left2) => Stay (make3 (left1, e', left2, e, right)))
          | EQUAL => Stay (make2 (left, update e, right))
          | GREATER =>
              (case modfy right of
                Stay right' => Stay (make2 (left, e, right'))
              | Sprout (right1, e', right2) =>
                  Stay (make3 (left, e, right1, e', right2))))
      | modfy (Branch3 (left, e1, mid, e2, right)) =
          (case compare e1 of
            LESS =>
              (case modfy left of
                Stay left' => Stay (make3 (left', e1, mid, e2, right))
              | Sprout (left1, e', left2) =>
                  Sprout (make2 (left1, e', left2), e1, make2 (mid, e2, right)))
          | EQUAL => Stay (make3 (left, update e1, mid, e2, right))
          | GREATER =>
              (case compare e2 of
                LESS =>
                  (case modfy mid of
                    Stay mid' => Stay (make3 (left, e1, mid', e2, right))
                  | Sprout (mid1, e', mid2) =>
                      Sprout (make2 (left, e1, mid1), e', make2 (mid2, e2, right)))
              | EQUAL => Stay (make3 (left, e1, mid, update e2, right))
              | GREATER =>
                  (case modfy right of
                    Stay right' => Stay (make3 (left, e1, mid, e2, right'))
                  | Sprout (right1, q, right2) =>
                      Sprout (make2 (left, e1, mid), e2, make2 (right1, q, right2)))))
      | modfy (Size (_, arg)) = modfy arg;

    val tab' =
      (case tab of
        Empty => Leaf1 (insert key)
      | Leaf1 e =>
          (case compare e of
            LESS => Leaf2 (insert key, e)
          | EQUAL => Leaf1 (update e)
          | GREATER => Leaf2 (e, insert key))
      | Leaf2 (e1, e2) =>
          (case compare e1 of
            LESS => Leaf3 (insert key, e1, e2)
          | EQUAL => Leaf2 (update e1, e2)
          | GREATER =>
              (case compare e2 of
                LESS => Leaf3 (e1, insert key, e2)
              | EQUAL => Leaf2 (e1, update e2)
              | GREATER => Leaf3 (e1, e2, insert key)))
      | _ =>
          (case modfy tab of
            Stay tab' => tab'
          | Sprout br => make2 br));
  in
    make_size (size tab + !inc) tab'
  end handle SAME => tab;

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

fun del (SOME k) Empty = raise UNDEF k
  | del NONE Empty = raise Match
  | del NONE (Leaf1 e) = (e, (true, Empty))
  | del NONE (Leaf2 (e1, e2)) = (e1, (false, Leaf1 e2))
  | del k (Leaf1 e) =
      (case compare k e of
        EQUAL => (e, (true, Empty))
      | _ => raise UNDEF (the k))
  | del k (Leaf2 (e1, e2)) =
      (case compare k e1 of
        EQUAL => (e1, (false, Leaf1 e2))
      | _ =>
        (case compare k e2 of
          EQUAL => (e2, (false, Leaf1 e1))
        | _ => raise UNDEF (the k)))
  | del k (Leaf3 (e1, e2, e3)) = del k (Branch2 (Leaf1 e1, e2, Leaf1 e3))
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
                  make2 (mr, if_equal ord q' q, r'))))))
  | del k (Size (_, arg)) = del k arg;
in

fun delete key tab = make_size (size tab - 1) (snd (snd (del (SOME key) tab)));
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

fun make_distinct entries = build (fold default entries);

fun make entries = build (fold update_new entries);

fun join f (tab1, tab2) =
  let
    fun add (key, y) tab = modify key (fn NONE => y | SOME x => f key (x, y)) tab;
  in
    if pointer_eq (tab1, tab2) then tab1
    else if is_empty tab1 then tab2
    else fold_table add tab2 tab1
  end;

fun merge eq = join (fn key => fn xy => if eq xy then raise SAME else raise DUP key);

fun joins f tabs = Library.foldl (join f) (empty, tabs);
fun merges eq tabs = Library.foldl (merge eq) (empty, tabs);


(* list tables *)

fun lookup_list tab key = these (lookup tab key);

fun cons_list (key, x) tab = modify key (fn NONE => [x] | SOME xs => x :: xs) tab;

fun modify_list key f =
  modify key (fn arg =>
    let
      val xs = the_default [] arg;
      val ys = f xs;
    in if pointer_eq (xs, ys) then raise SAME else ys end);

fun insert_list eq (key, x) = modify_list key (Library.insert eq x);
fun update_list eq (key, x) = modify_list key (Library.update eq x);

fun remove_list eq (key, x) tab =
  map_entry key (fn xs =>
    (case Library.remove eq x xs of
      [] => raise UNDEF key
    | ys => if pointer_eq (xs, ys) then raise SAME else ys)) tab
  handle UNDEF _ => delete key tab;

fun make_list args = build (fold_rev cons_list args);
fun dest_list tab = maps (fn (key, xs) => map (pair key) xs) (dest tab);
fun merge_list eq =
  join (fn _ => fn xy => if eq_list eq xy then raise SAME else Library.merge eq xy);


(* set operations *)

type set = unit table;

fun insert_set x = default (x, ());
fun remove_set x : set -> set = delete_safe x;
fun make_set xs = build (fold insert_set xs);


(* cache *)

type 'a cache_ops = {apply: key -> 'a, reset: unit -> unit};

fun unsynchronized_cache f =
  let
    val cache1 = Unsynchronized.ref empty;
    val cache2 = Unsynchronized.ref empty;
    fun apply x =
      (case lookup (! cache1) x of
        SOME y => y
      | NONE =>
          (case lookup (! cache2) x of
            SOME exn => Exn.reraise exn
          | NONE =>
              (case Exn.result f x of
                Exn.Res y => (Unsynchronized.change cache1 (update (x, y)); y)
              | Exn.Exn exn => (Unsynchronized.change cache2 (update (x, exn)); Exn.reraise exn))));
    fun reset () = (cache2 := empty; cache1 := empty);
  in {apply = apply, reset = reset} end;


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
