(*  Title:      Pure/term_items.ML
    Author:     Makarius

Scalable collections of term items:
  - table: e.g. for instantiation
  - set with order of addition, e.g. occurrences within term
*)

signature TERM_ITEMS =
sig
  type key
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
  val add: key * 'a -> 'a table -> 'a table
  val make: (key * 'a) list -> 'a table
  type set = int table
  val add_set: key -> set -> set
  val make_set: key list -> set
  val list_set: set -> key list
  val list_set_rev: set -> key list
  val subset: set * set -> bool
  val eq_set: set * set -> bool
end;

functor Term_Items(Key: KEY): TERM_ITEMS =
struct

(* table with length *)

structure Table = Table(Key);

type key = Table.key;
datatype 'a table = Items of int * 'a Table.table;

fun size (Items (n, _)) = n;
fun table (Items (_, tab)) = tab;

val empty = Items (0, Table.empty);
fun build (f: 'a table -> 'a table) = f empty;
fun is_empty items = size items = 0;

fun dest items = Table.dest (table items);
fun keys items = Table.keys (table items);
fun exists pred = Table.exists pred o table;
fun forall pred = Table.forall pred o table;
fun get_first get = Table.get_first get o table;
fun lookup items = Table.lookup (table items);
fun defined items = Table.defined (table items);

fun add (key, x) (items as Items (n, tab)) =
  if Table.defined tab key then items
  else Items (n + 1, Table.update_new (key, x) tab);

fun make entries = build (fold add entries);


(* set with order of addition *)

type set = int table;

fun add_set x (items as Items (n, tab)) =
  if Table.defined tab x then items
  else Items (n + 1, Table.update_new (x, n) tab);

fun make_set xs = build (fold add_set xs);

fun subset (A: set, B: set) = forall (defined B o #1) A;
fun eq_set (A: set, B: set) = size A = size B andalso subset (A, B);

fun list_set_ord ord items = Table.dest (table items) |> sort (ord o apply2 #2) |> map #1
val list_set = list_set_ord int_ord;
val list_set_rev = list_set_ord (rev_order o int_ord);

fun map f (Items (n, tab)) = Items (n, Table.map f tab);
fun fold f = Table.fold f o table;
fun fold_rev f = Table.fold_rev f o table;

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
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Term_Ord.typ_ord)
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
  val ord = fast_string_ord
);
open Term_Items;

val add_tfree_namesT = fold_atyps (fn TFree (a, _) => add_set a | _ => I);
val add_tfree_names = fold_types add_tfree_namesT;
val add_free_names = fold_aterms (fn Free (x, _) => add_set x | _ => I);

end;
