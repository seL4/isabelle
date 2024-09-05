(*  Title:      Pure/General/set.ML
    Author:     Makarius

Efficient representation of sets (see also Pure/General/table.ML).
*)

signature SET =
sig
  structure Key: KEY
  type elem
  type T
  val size: T -> int
  val empty: T
  val build: (T -> T) -> T
  val is_empty: T -> bool
  val fold: (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val fold_rev: (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val dest: T -> elem list
  val min: T -> elem option
  val max: T -> elem option
  val exists: (elem -> bool) -> T -> bool
  val forall: (elem -> bool) -> T -> bool
  val get_first: (elem -> 'a option) -> T -> 'a option
  val member: T -> elem -> bool
  val subset: T * T -> bool
  val eq_set: T * T -> bool
  val ord: T ord
  val insert: elem -> T -> T
  val make: elem list -> T
  val merge: T * T -> T
  val merges: T list -> T
  val remove: elem -> T -> T
  val subtract: T -> T -> T
  val restrict: (elem -> bool) -> T -> T
  val inter: T -> T -> T
  val union: T -> T -> T
end;

functor Set(Key: KEY): SET =
struct

(* keys *)

structure Key = Key;
type elem = Key.key;


(* datatype *)

datatype T =
  Empty |
  Leaf1 of elem |
  Leaf2 of elem * elem |
  Leaf3 of elem * elem * elem |
  Branch2 of T * elem * T |
  Branch3 of T * elem * T * elem * T |
  Size of int * T;

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
  | unmake (Leaf3 (e1, e2, e3)) =
      Branch2 (Branch2 (Empty, e1, Empty), e2, Branch2 (Empty, e3, Empty))
  | unmake (Size (_, arg)) = arg
  | unmake arg = arg;


(* size *)

(*literal copy from table.ML*)
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

fun build (f: T -> T) = f empty;

(*literal copy from table.ML*)
fun is_empty Empty = true
  | is_empty (Size (_, arg)) = is_empty arg
  | is_empty _ = false;


(* fold combinators *)

fun fold_set f =
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

fun fold_rev_set f =
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

val dest = Library.build o fold_rev_set cons;


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


(* member and subset *)

fun member set elem =
  let
    fun elem_ord e = Key.ord (elem, e)
    val elem_eq = is_equal o elem_ord;

    fun mem Empty = false
      | mem (Leaf1 e) = elem_eq e
      | mem (Leaf2 (e1, e2)) =
          (case elem_ord e1 of
            LESS => false
          | EQUAL => true
          | GREATER => elem_eq e2)
      | mem (Leaf3 (e1, e2, e3)) =
          (case elem_ord e2 of
            LESS => elem_eq e1
          | EQUAL => true
          | GREATER => elem_eq e3)
      | mem (Branch2 (left, e, right)) =
          (case elem_ord e of
            LESS => mem left
          | EQUAL => true
          | GREATER => mem right)
      | mem (Branch3 (left, e1, mid, e2, right)) =
          (case elem_ord e1 of
            LESS => mem left
          | EQUAL => true
          | GREATER =>
              (case elem_ord e2 of
                LESS => mem mid
              | EQUAL => true
              | GREATER => mem right))
      | mem (Size (_, arg)) = mem arg;
  in mem set end;

fun subset (set1, set2) = forall (member set2) set1;


(* equality and order *)

fun eq_set (set1, set2) =
  pointer_eq (set1, set2) orelse size set1 = size set2 andalso subset (set1, set2);

val ord =
  pointer_eq_ord (fn (set1, set2) =>
    (case int_ord (size set1, size set2) of
      EQUAL =>
        (case get_first (fn a => if member set2 a then NONE else SOME a) set1 of
          NONE => EQUAL
        | SOME a =>
            (case get_first (fn b => if member set1 b then NONE else SOME b) set2 of
              NONE => EQUAL
            | SOME b => Key.ord (a, b)))
    | order => order));


(* insert *)

datatype growth = Stay of T | Sprout of T * elem * T;

fun insert elem set =
  if member set elem then set
  else
    let
      fun elem_ord e = Key.ord (elem, e);
      val elem_less = is_less o elem_ord;

      fun ins Empty = Sprout (Empty, elem, Empty)
        | ins (t as Leaf1 _) = ins (unmake t)
        | ins (t as Leaf2 _) = ins (unmake t)
        | ins (t as Leaf3 _) = ins (unmake t)
        | ins (Branch2 (left, e, right)) =
            (case elem_ord e of
              LESS =>
                (case ins left of
                  Stay left' => Stay (make2 (left', e, right))
                | Sprout (left1, e', left2) => Stay (make3 (left1, e', left2, e, right)))
            | EQUAL => Stay (make2 (left, e, right))
            | GREATER =>
                (case ins right of
                  Stay right' => Stay (make2 (left, e, right'))
                | Sprout (right1, e', right2) =>
                    Stay (make3 (left, e, right1, e', right2))))
        | ins (Branch3 (left, e1, mid, e2, right)) =
            (case elem_ord e1 of
              LESS =>
                (case ins left of
                  Stay left' => Stay (make3 (left', e1, mid, e2, right))
                | Sprout (left1, e', left2) =>
                    Sprout (make2 (left1, e', left2), e1, make2 (mid, e2, right)))
            | EQUAL => Stay (make3 (left, e1, mid, e2, right))
            | GREATER =>
                (case elem_ord e2 of
                  LESS =>
                    (case ins mid of
                      Stay mid' => Stay (make3 (left, e1, mid', e2, right))
                    | Sprout (mid1, e', mid2) =>
                        Sprout (make2 (left, e1, mid1), e', make2 (mid2, e2, right)))
                | EQUAL => Stay (make3 (left, e1, mid, e2, right))
                | GREATER =>
                    (case ins right of
                      Stay right' => Stay (make3 (left, e1, mid, e2, right'))
                    | Sprout (right1, e', right2) =>
                        Sprout (make2 (left, e1, mid), e2, make2 (right1, e', right2)))))
        | ins (Size (_, arg)) = ins arg;
    in
      (case set of
        Empty => Leaf1 elem
      | Leaf1 e =>
          if elem_less e
          then Leaf2 (elem, e)
          else Leaf2 (e, elem)
      | Leaf2 (e1, e2) =>
          if elem_less e1
          then Leaf3 (elem, e1, e2)
          else if elem_less e2
          then Leaf3 (e1, elem, e2)
          else Leaf3 (e1, e2, elem)
      | _ =>
          make_size (size set + 1)
            (case ins set of
              Stay set' => set'
            | Sprout br => make2 br))
    end;

fun make elems = build (fold insert elems);


(* merge *)

fun merge (set1, set2) =
  if pointer_eq (set1, set2) then set1
  else if is_empty set1 then set2
  else if is_empty set2 then set1
  else if size set1 >= size set2
  then fold_set insert set2 set1
  else fold_set insert set1 set2;

fun merges sets = Library.foldl merge (empty, sets);


(* remove *)

local

fun compare NONE _ = LESS
  | compare (SOME e1) e2 = Key.ord (e1, e2);

fun if_equal ord x y = if is_equal ord then x else y;

exception UNDEF of elem;

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
                  make2 (mr, if_equal ord q' q, r'))))))
  | del k (Size (_, arg)) = del k arg;

in

fun remove elem set =
  if member set elem
  then make_size (size set - 1) (snd (snd (del (SOME elem) set)))
  else set;

val subtract = fold_set remove;

end;


(* conventional set operations *)

fun restrict pred set =
  fold_set (fn x => not (pred x) ? remove x) set set;

fun inter set1 set2 =
  if pointer_eq (set1, set2) then set1
  else if is_empty set1 orelse is_empty set2 then empty
  else if size set1 < size set2 then restrict (member set2) set1
  else restrict (member set1) set2;

fun union set1 set2 = merge (set2, set1);


(* ML pretty-printing *)

val _ =
  ML_system_pp (fn depth => fn _ => fn set =>
    ML_Pretty.enum "," "{" "}" ML_system_pretty (dest set, depth));

(*final declarations of this structure!*)
val fold = fold_set;
val fold_rev = fold_rev_set;

end;

structure Intset = Set(Inttab.Key);
structure Symset = Set(Symtab.Key);
