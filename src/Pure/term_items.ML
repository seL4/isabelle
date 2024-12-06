(*  Title:      Pure/term_items.ML
    Author:     Makarius

Scalable collections of term items:
  - table: e.g. for instantiation
  - set with order of addition, e.g. occurrences within term
*)

signature TERM_ITEMS =
sig
  structure Key: KEY
  type key
  exception DUP of key
  type 'a table
  val empty: 'a table
  val build: ('a table -> 'a table) -> 'a table
  val size: 'a table -> int
  val is_empty: 'a table -> bool
  val map: (key -> 'a -> 'b) -> 'a table -> 'b table
  val fold: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val fold_rev: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val forall: (key * 'a -> bool) -> 'a table -> bool
  val get_first: (key * 'a -> 'b option) -> 'a table -> 'b option
  val lookup: 'a table -> key -> 'a option
  val defined: 'a table -> key -> bool
  val update: key * 'a -> 'a table -> 'a table
  val remove: key -> 'a table -> 'a table
  val insert: ('a * 'a -> bool) -> key * 'a -> 'a table -> 'a table    (*exception DUP*)
  val add: key * 'a -> 'a table -> 'a table
  val make: (key * 'a) list -> 'a table
  val make1: key * 'a -> 'a table
  val make2: key * 'a -> key * 'a -> 'a table
  val make3: key * 'a -> key * 'a -> key * 'a -> 'a table
  type 'a cache_ops = {apply: key -> 'a, reset: unit -> unit, size: unit -> int};
  val unsynchronized_cache: (key -> 'a) -> 'a cache_ops
  val apply_unsynchronized_cache: (key -> 'a) -> key -> 'a
  type set = int table
  val add_set: key -> set -> set
  val make_set: key list -> set
  val make1_set: key -> set
  val make2_set: key -> key -> set
  val make3_set: key -> key -> key -> set
  val list_set: set -> key list
  val list_set_rev: set -> key list
  val subset: set * set -> bool
  val eq_set: set * set -> bool
end;

functor Term_Items(Key: KEY): TERM_ITEMS =
struct

(* keys *)

structure Key = Key;
type key = Key.key;


(* table with length *)

structure Table = Table(Key);
exception DUP = Table.DUP;

datatype 'a table = Table of 'a Table.table;

val empty = Table Table.empty;
fun build (f: 'a table -> 'a table) = f empty;
fun is_empty (Table tab) = Table.is_empty tab;

fun size (Table tab) = Table.size tab;
fun dest (Table tab) = Table.dest tab;
fun keys (Table tab) = Table.keys tab;
fun exists pred (Table tab) = Table.exists pred tab;
fun forall pred (Table tab) = Table.forall pred tab;
fun get_first get (Table tab) = Table.get_first get tab;
fun lookup (Table tab) = Table.lookup tab;
fun defined (Table tab) = Table.defined tab;

fun update e (Table tab) = Table (Table.update e tab);
fun remove x (Table tab) = Table (Table.delete_safe x tab);
fun insert eq e (Table tab) = Table (Table.insert eq e tab);

fun add entry (Table tab) = Table (Table.default entry tab);
fun make es = build (fold add es);
fun make1 e = build (add e);
fun make2 e1 e2 = build (add e1 #> add e2);
fun make3 e1 e2 e3 = build (add e1 #> add e2 #> add e3);

type 'a cache_ops = 'a Table.cache_ops;
val unsynchronized_cache = Table.unsynchronized_cache;
val apply_unsynchronized_cache = Table.apply_unsynchronized_cache;


(* set with order of addition *)

type set = int table;

fun add_set x (Table tab) =
  Table (if Table.defined tab x then tab else Table.update_new (x, Table.size tab + 1) tab);

fun make_set xs = build (fold add_set xs);
fun make1_set e = build (add_set e);
fun make2_set e1 e2 = build (add_set e1 #> add_set e2);
fun make3_set e1 e2 e3 = build (add_set e1 #> add_set e2 #> add_set e3);

fun subset (A: set, B: set) = forall (defined B o #1) A;
fun eq_set (A: set, B: set) = pointer_eq (A, B) orelse size A = size B andalso subset (A, B);

fun list_set_ord ord (Table tab) = tab |> Table.dest |> sort (ord o apply2 #2) |> map #1;
val list_set = list_set_ord int_ord;
val list_set_rev = list_set_ord (rev_order o int_ord);

fun map f (Table tab) = Table (Table.map f tab);
fun fold f (Table tab) = Table.fold f tab;
fun fold_rev f (Table tab) = Table.fold_rev f tab;

end;


structure TFrees:
sig
  include TERM_ITEMS
  val add_tfreesT: typ -> set -> set
  val add_tfrees: term -> set -> set
  val add_tfreesT_unless: (string * sort -> bool) -> typ -> set -> set
  val add_tfrees_unless: (string * sort -> bool) -> term -> set -> set
end =
struct

structure Items = Term_Items
(
  type key = string * sort;
  val ord = pointer_eq_ord (prod_ord fast_string_ord Term_Ord.sort_ord);
);
open Items;

val add_tfreesT = fold_atyps (fn TFree v => add_set v | _ => I);
val add_tfrees = fold_types add_tfreesT;

fun add_tfreesT_unless pred = Term.fold_atyps (fn TFree v => not (pred v) ? add_set v | _ => I);
fun add_tfrees_unless pred = fold_types (add_tfreesT_unless pred);

end;


structure TVars:
sig
  include TERM_ITEMS
  val add_tvarsT: typ -> set -> set
  val add_tvars: term -> set -> set
end =
struct

structure Term_Items = Term_Items(
  type key = indexname * sort;
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Term_Ord.sort_ord);
);
open Term_Items;

val add_tvarsT = fold_atyps (fn TVar v => add_set v | _ => I);
val add_tvars = fold_types add_tvarsT;

end;


structure Frees:
sig
  include TERM_ITEMS
  val add_frees: term -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = string * typ;
  val ord = pointer_eq_ord (prod_ord fast_string_ord Term_Ord.typ_ord);
);
open Term_Items;

val add_frees = fold_aterms (fn Free v => add_set v | _ => I);

end;


structure Vars:
sig
  include TERM_ITEMS
  val add_vars: term -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = indexname * typ;
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Term_Ord.typ_ord);
);
open Term_Items;

val add_vars = fold_aterms (fn Var v => add_set v | _ => I);

end;


structure Names:
sig
  include TERM_ITEMS
  val add_tfree_namesT: typ -> set -> set
  val add_tfree_names: term -> set -> set
  val add_free_names: term -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = string;
  val ord = fast_string_ord;
);
open Term_Items;

val add_tfree_namesT = fold_atyps (fn TFree (a, _) => add_set a | _ => I);
val add_tfree_names = fold_types add_tfree_namesT;
val add_free_names = fold_aterms (fn Free (x, _) => add_set x | _ => I);

end;


structure Indexnames: TERM_ITEMS = Term_Items
(
  type key = indexname;
  val ord = Term_Ord.fast_indexname_ord;
);


structure Types:
sig
  include TERM_ITEMS
  val add_atyps: term -> set -> set
end =
struct

structure Term_Items = Term_Items(type key = typ val ord = Term_Ord.typ_ord);
open Term_Items;

val add_atyps = (fold_types o fold_atyps) add_set;

end;
