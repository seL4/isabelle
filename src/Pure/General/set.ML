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
  val is_single: T -> bool
  val fold: (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val fold_rev: (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val dest: T -> elem list
  val exists: (elem -> bool) -> T -> bool
  val forall: (elem -> bool) -> T -> bool
  val get_first: (elem -> 'a option) -> T -> 'a option
  val member: T -> elem -> bool
  val subset: T * T -> bool
  val ord: T ord
  val insert: elem -> T -> T
  val make: elem list -> T
  val merge: T * T -> T
  val remove: elem -> T -> T
  val subtract: T -> T -> T
end;

functor Set(Key: KEY): SET =
struct

structure Key = Key;
type elem = Key.key;


(* datatype *)

datatype T =
  Empty |
  Branch2 of T * elem * T |
  Branch3 of T * elem * T * elem * T;


(* size *)

local
  fun add_size Empty n = n
    | add_size (Branch2 (left, _, right)) n =
        n + 1 |> add_size left |> add_size right
    | add_size (Branch3 (left, _, mid, _, right)) n =
        n + 2 |> add_size left |> add_size mid |> add_size right;
in
  fun size set = add_size set 0;
end;


(* empty and single *)

val empty = Empty;

fun build (f: T -> T) = f empty;

fun is_empty Empty = true
  | is_empty _ = false;

fun is_single (Branch2 (Empty, _, Empty)) = true
  | is_single _ = false;


(* fold combinators *)

fun fold_set f =
  let
    fun fold Empty x = x
      | fold (Branch2 (left, e, right)) x =
          fold right (f e (fold left x))
      | fold (Branch3 (left, e1, mid, e2, right)) x =
          fold right (f e2 (fold mid (f e1 (fold left x))));
  in fold end;

fun fold_rev_set f =
  let
    fun fold_rev Empty x = x
      | fold_rev (Branch2 (left, e, right)) x =
          fold_rev left (f e (fold_rev right x))
      | fold_rev (Branch3 (left, e1, mid, e2, right)) x =
          fold_rev left (f e1 (fold_rev mid (f e2 (fold_rev right x))));
  in fold_rev end;

fun dest tab = fold_rev_set cons tab [];


(* exists and forall *)

fun exists pred =
  let
    fun ex Empty = false
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


(* member *)

fun member set elem =
  let
    fun mem Empty = false
      | mem (Branch2 (left, e, right)) =
          (case Key.ord (elem, e) of
            LESS => mem left
          | EQUAL => true
          | GREATER => mem right)
      | mem (Branch3 (left, e1, mid, e2, right)) =
          (case Key.ord (elem, e1) of
            LESS => mem left
          | EQUAL => true
          | GREATER =>
              (case Key.ord (elem, e2) of
                LESS => mem mid
              | EQUAL => true
              | GREATER => mem right));
  in mem set end;


(* subset and order *)

fun subset (set1, set2) = forall (member set2) set1;

val ord =
  pointer_eq_ord (fn sets =>
    (case int_ord (apply2 size sets) of
      EQUAL =>
        if subset sets then EQUAL
        else dict_ord Key.ord (apply2 dest sets)
    | ord => ord));


(* insert *)

datatype growth = Stay of T | Sprout of T * elem * T;

fun insert elem set =
  if member set elem then set
  else
    let
      fun ins Empty = Sprout (Empty, elem, Empty)
        | ins (Branch2 (left, e, right)) =
            (case Key.ord (elem, e) of
              LESS =>
                (case ins left of
                  Stay left' => Stay (Branch2 (left', e, right))
                | Sprout (left1, e', left2) => Stay (Branch3 (left1, e', left2, e, right)))
            | EQUAL => Stay (Branch2 (left, e, right))
            | GREATER =>
                (case ins right of
                  Stay right' => Stay (Branch2 (left, e, right'))
                | Sprout (right1, e', right2) =>
                    Stay (Branch3 (left, e, right1, e', right2))))
        | ins (Branch3 (left, e1, mid, e2, right)) =
            (case Key.ord (elem, e1) of
              LESS =>
                (case ins left of
                  Stay left' => Stay (Branch3 (left', e1, mid, e2, right))
                | Sprout (left1, e', left2) =>
                    Sprout (Branch2 (left1, e', left2), e1, Branch2 (mid, e2, right)))
            | EQUAL => Stay (Branch3 (left, e1, mid, e2, right))
            | GREATER =>
                (case Key.ord (elem, e2) of
                  LESS =>
                    (case ins mid of
                      Stay mid' => Stay (Branch3 (left, e1, mid', e2, right))
                    | Sprout (mid1, e', mid2) =>
                        Sprout (Branch2 (left, e1, mid1), e', Branch2 (mid2, e2, right)))
                | EQUAL => Stay (Branch3 (left, e1, mid, e2, right))
                | GREATER =>
                    (case ins right of
                      Stay right' => Stay (Branch3 (left, e1, mid, e2, right'))
                    | Sprout (right1, e', right2) =>
                        Sprout (Branch2 (left, e1, mid), e2, Branch2 (right1, e', right2)))));
    in
      (case ins set of
        Stay set' => set'
      | Sprout br => Branch2 br)
    end;

fun make elems = build (fold insert elems);

fun merge (set1, set2) =
  if pointer_eq (set1, set2) then set1
  else if is_empty set1 then set2
  else if is_empty set2 then set1
  else if size set1 >= size set2
  then fold_set insert set2 set1
  else fold_set insert set1 set2;


(* remove *)

local

fun compare NONE _ = LESS
  | compare (SOME e1) e2 = Key.ord (e1, e2);

fun if_eq EQUAL x y = x
  | if_eq _ x y = y;

exception UNDEF of elem;

(*literal copy from table.ML -- by Stefan Berghofer*)
fun del (SOME k) Empty = raise UNDEF k
  | del NONE (Branch2 (Empty, p, Empty)) = (p, (true, Empty))
  | del NONE (Branch3 (Empty, p, Empty, q, Empty)) =
      (p, (false, Branch2 (Empty, q, Empty)))
  | del k (Branch2 (Empty, p, Empty)) =
      (case compare k p of
        EQUAL => (p, (true, Empty))
      | _ => raise UNDEF (the k))
  | del k (Branch3 (Empty, p, Empty, q, Empty)) =
      (case compare k p of
        EQUAL => (p, (false, Branch2 (Empty, q, Empty)))
      | _ =>
        (case compare k q of
          EQUAL => (q, (false, Branch2 (Empty, p, Empty)))
        | _ => raise UNDEF (the k)))
  | del k (Branch2 (l, p, r)) =
      (case compare k p of
        LESS =>
          (case del k l of
            (p', (false, l')) => (p', (false, Branch2 (l', p, r)))
          | (p', (true, l')) => (p', case r of
              Branch2 (rl, rp, rr) =>
                (true, Branch3 (l', p, rl, rp, rr))
            | Branch3 (rl, rp, rm, rq, rr) => (false, Branch2
                (Branch2 (l', p, rl), rp, Branch2 (rm, rq, rr)))))
      | ord =>
          (case del (if_eq ord NONE k) r of
            (p', (false, r')) => (p', (false, Branch2 (l, if_eq ord p' p, r')))
          | (p', (true, r')) => (p', case l of
              Branch2 (ll, lp, lr) =>
                (true, Branch3 (ll, lp, lr, if_eq ord p' p, r'))
            | Branch3 (ll, lp, lm, lq, lr) => (false, Branch2
                (Branch2 (ll, lp, lm), lq, Branch2 (lr, if_eq ord p' p, r'))))))
  | del k (Branch3 (l, p, m, q, r)) =
      (case compare k q of
        LESS =>
          (case compare k p of
            LESS =>
              (case del k l of
                (p', (false, l')) => (p', (false, Branch3 (l', p, m, q, r)))
              | (p', (true, l')) => (p', (false, case (m, r) of
                  (Branch2 (ml, mp, mr), Branch2 _) =>
                    Branch2 (Branch3 (l', p, ml, mp, mr), q, r)
                | (Branch3 (ml, mp, mm, mq, mr), _) =>
                    Branch3 (Branch2 (l', p, ml), mp, Branch2 (mm, mq, mr), q, r)
                | (Branch2 (ml, mp, mr), Branch3 (rl, rp, rm, rq, rr)) =>
                    Branch3 (Branch2 (l', p, ml), mp, Branch2 (mr, q, rl), rp,
                      Branch2 (rm, rq, rr)))))
          | ord =>
              (case del (if_eq ord NONE k) m of
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
      | ord =>
          (case del (if_eq ord NONE k) r of
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

fun remove elem set =
  if member set elem then snd (snd (del (SOME elem) set)) else set;

val subtract = fold_set remove;

end;


(* ML pretty-printing *)

val _ =
  ML_system_pp (fn depth => fn _ => fn set =>
    ML_Pretty.to_polyml
      (ML_Pretty.enum "," "{" "}" (ML_Pretty.from_polyml o ML_system_pretty) (dest set, depth)));


(*final declarations of this structure!*)
val fold = fold_set;
val fold_rev = fold_rev_set;

end;

structure Intset = Set(Inttab.Key);
structure Symset = Set(Symtab.Key);
