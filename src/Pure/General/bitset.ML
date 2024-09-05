(*  Title:      Pure/General/bitset.ML
    Author:     Makarius

Compact representation of sets of integers.
*)

signature BITSET =
sig
  type elem = int
  val make_elem: int * int -> elem  (*exception*)
  val dest_elem: elem -> int * int
  type T
  val empty: T
  val build: (T -> T) -> T
  val is_empty: T -> bool
  val fold: (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val fold_rev: (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val dest: T -> elem list
  val is_unique: T -> bool
  val min: T -> elem option
  val max: T -> elem option
  val get_first: (elem -> 'a option) -> T -> 'a option
  val exists: (elem -> bool) -> T -> bool
  val forall: (elem -> bool) -> T -> bool
  val member: T -> elem -> bool
  val subset: T * T -> bool
  val eq_set: T * T -> bool
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

structure Bitset: BITSET =
struct

(* bits and words *)

exception BAD of int;

val word_size = Word.wordSize;

val min_bit = 0;
val max_bit = word_size - 1;
fun check_bit n = min_bit <= n andalso n <= max_bit;

fun make_bit n = if check_bit n then Word.<< (0w1, Word.fromInt n) else raise BAD n;
val mimimum_bit = make_bit min_bit;
val maximum_bit = make_bit max_bit;

fun add_bits v w = Word.orb (v, w);
fun del_bits v w = Word.andb (Word.notb v, w);
fun incl_bits v w = add_bits v w = w;

fun fold_bits f w =
  let
    fun app n b a = if incl_bits b w then f n a else a;
    fun bits n b a =
      if n = max_bit then app n b a
      else bits (n + 1) (Word.<< (b, 0w1)) (app n b a);
  in bits min_bit mimimum_bit end;

fun fold_rev_bits f w =
  let
    fun app n b a = if incl_bits b w then f n a else a;
    fun bits n b a =
      if n = min_bit then app n b a
      else bits (n - 1) (Word.>> (b, 0w1)) (app n b a);
  in bits max_bit maximum_bit end;


(* datatype *)

type elem = int;

fun make_elem (m, n) : elem = if check_bit n then m * word_size + n else raise BAD n;
fun dest_elem (x: elem) = Integer.div_mod x word_size;

datatype T = Bitset of word Inttab.table;


(* empty *)

val empty = Bitset Inttab.empty;

fun build (f: T -> T) = f empty;

fun is_empty (Bitset t) = Inttab.is_empty t;


(* fold combinators *)

fun fold_set f (Bitset t) =
  Inttab.fold (fn (m, w) =>
    (if m < 0 then fold_rev_bits else fold_bits) (fn n => f (make_elem (m, n))) w) t;

fun fold_rev_set f (Bitset t) =
  Inttab.fold_rev (fn (m, w) =>
    (if m < 0 then fold_bits else fold_rev_bits) (fn n => f (make_elem (m, n))) w) t;

val dest = Library.build o fold_rev_set cons;

fun is_unique (set as Bitset t) =
  is_empty set orelse
  Inttab.size t = 1 andalso fold_set (fn _ => Integer.add 1) set 0 = 1;


(* min/max entries *)

fun min (Bitset t) =
  Inttab.min t |> Option.map (fn (m, w) =>
    make_elem (m, fold_bits Integer.min w max_bit));

fun max (Bitset t) =
  Inttab.max t |> Option.map (fn (m, w) =>
    make_elem (m, fold_bits Integer.max w min_bit));


(* linear search *)

fun get_first f set =
  let exception FOUND of 'a in
    fold_set (fn x => fn a => (case f x of SOME b => raise FOUND b | NONE => a)) set NONE
      handle FOUND b => SOME b
  end;

fun exists pred = is_some o get_first (fn x => if pred x then SOME x else NONE);
fun forall pred = not o exists (not o pred);


(* member *)

fun member (Bitset t) x =
  let val (m, n) = dest_elem x in
    (case Inttab.lookup t m of
      NONE => false
    | SOME w => incl_bits (make_bit n) w)
  end;


(* subset *)

fun subset (Bitset t1, Bitset t2) =
  pointer_eq (t1, t2) orelse
    Inttab.size t1 <= Inttab.size t2 andalso
    t1 |> Inttab.forall (fn (m, w1) =>
      (case Inttab.lookup t2 m of
        NONE => false
      | SOME w2 => incl_bits w1 w2));

fun eq_set (set1, set2) =
  pointer_eq (set1, set2) orelse subset (set1, set2) andalso subset (set2, set1);


(* insert *)

fun insert x (Bitset t) =
  let val (m, n) = dest_elem x
  in Bitset (Inttab.map_default (m, 0w0) (add_bits (make_bit n)) t) end;

fun make xs = build (fold insert xs);


(* merge *)

fun join_bits (w1, w2) =
  let val w = add_bits w2 w1
  in if w = w1 then raise Inttab.SAME else w end;

fun merge (set1 as Bitset t1, set2 as Bitset t2) =
  if pointer_eq (set1, set2) then set1
  else if is_empty set1 then set2
  else if is_empty set2 then set1
  else Bitset (Inttab.join (K join_bits) (t1, t2));

fun merges sets = Library.foldl merge (empty, sets);


(* remove *)

fun remove x (set as Bitset t) =
  let val (m, n) = dest_elem x in
    (case Inttab.lookup t m of
      NONE => set
    | SOME w =>
        let val w' = del_bits (make_bit n) w in
          if w = w' then set
          else if w' = 0w0 then Bitset (Inttab.delete m t)
          else Bitset (Inttab.update (m, w') t)
        end)
  end;

val subtract = fold_set remove;


(* conventional set operations *)

fun restrict pred set =
  fold_set (fn x => not (pred x) ? remove x) set set;

fun inter set1 set2 =
  if pointer_eq (set1, set2) then set1
  else if is_empty set1 orelse is_empty set2 then empty
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
