(*  Title:      Pure/General/graph.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Directed graphs.
*)

signature GRAPH =
sig
  type key
  type 'a T
  exception UNDEFINED of key
  exception DUPLICATE of key
  exception CYCLES of key list list
  val empty: 'a T
  val map : ('a -> 'b) -> 'a T -> 'b T
  val foldl : ('a * (key * ('b * (key list * key list))) -> 'a) -> 'a * 'b T -> 'a
  val info: 'a T -> key -> 'a
  val map_info: ('a -> 'a) -> key -> 'a T -> 'a T
  val preds: 'a T -> key -> key list
  val succs: 'a T -> key -> key list
  val all_preds: 'a T -> key list -> key list
  val all_succs: 'a T -> key list -> key list
  val find_paths: 'a T -> key * key -> key list list
  val add_node: key * 'a -> 'a T -> 'a T
  val add_edge: key * key -> 'a T -> 'a T
  val add_edge_acyclic: key * key -> 'a T -> 'a T
  val derive_node: key * 'a -> key list -> 'a T -> 'a T
end;

functor GraphFun(Key: KEY): GRAPH =
struct


(* keys *)

type key = Key.key;

val eq_key = equal EQUAL o Key.ord;

infix mem_key;
val op mem_key = gen_mem eq_key;

infix ins_key;
val op ins_key = gen_ins eq_key;


(* tables and sets of keys *)

structure Table = TableFun(Key);
type keys = unit Table.table;

infix mem_keys;
fun x mem_keys tab = is_some (Table.lookup (tab: keys, x));

infix ins_keys;
fun x ins_keys tab = if x mem_keys tab then tab else Table.update ((x, ()), tab);

val empty_keys = Table.empty: keys;
fun make_keys xs = foldl (fn (tab, x) => x ins_keys tab) (empty_keys, xs);
fun dest_keys tab = rev (Table.foldl (fn (xs, (x, ())) => x :: xs) ([], tab: keys));


(* datatype of graphs *)

datatype 'a T = Graph of ('a * (key list * key list)) Table.table;

exception UNDEFINED of key;
exception DUPLICATE of key;
exception CYCLES of key list list;


(* basic operations *)

fun map_graph f (Graph tab) = Graph (Table.map (fn (i, ps) => (f i, ps)) tab);
fun foldl_graph f (x, Graph tab) = Table.foldl f (x, tab);

val empty = Graph Table.empty;

fun get_node (Graph tab) x =
  (case Table.lookup (tab, x) of
    Some node => node
  | None => raise UNDEFINED x);

fun info G = #1 o get_node G;
fun preds G = #1 o #2 o get_node G;
fun succs G = #2 o #2 o get_node G;

fun map_node f x (G as Graph tab) =
  let val node = get_node G x
  in Graph (Table.update ((x, f node), tab)) end;

fun map_info f = map_node (fn (info, ps) => (f info, ps));


(* reachable nodes *)

fun reachable_keys next xs =
  let
    fun reach (R, x) =
      if x mem_keys R then R
      else reachs (x ins_keys R, next x)
    and reachs R_xs = foldl reach R_xs;
  in reachs (empty_keys, xs) end;

val reachable = dest_keys oo reachable_keys;

fun all_preds G = reachable (preds G);
fun all_succs G = reachable (succs G);


(* find_paths *)

fun find_paths G (x, y) =
  let
    val X = reachable_keys (succs G) [x];
    fun paths ps p =
      if eq_key (p, x) then [p :: ps]
      else flat (map (paths (p :: ps))
        (filter (fn pp => pp mem_keys X andalso not (pp mem_key ps)) (preds G p)));
  in if y mem_keys X then (paths [] y) else [] end;


(* build graphs *)

fun add_node (x, info) (Graph tab) =
  Graph (Table.update_new ((x, (info, ([], []))), tab)
    handle Table.DUP key => raise DUPLICATE key);

fun add_edge (x, y) G =
  (get_node G x; get_node G y;
    G |> map_node (fn (i, (preds, succs)) => (i, (preds, y ins_key succs))) x
      |> map_node (fn (i, (preds, succs)) => (i, (x ins_key preds, succs))) y);

fun add_edge_acyclic (x, y) G =
  (case find_paths G (y, x) of
    [] => add_edge (x, y) G
  | cycles => raise CYCLES (map (cons x) cycles));

fun derive_node (x, y) zs G =
  foldl (fn (H, z) => add_edge_acyclic (z, x) H) (add_node (x, y) G, zs);


(*final declarations of this structure!*)
val map = map_graph;
val foldl = foldl_graph;


end;


(*graphs indexed by strings*)
structure Graph = GraphFun(type key = string val ord = string_ord);
