(*  Title:      Pure/General/graph.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Directed graphs.
*)

signature GRAPH =
sig
  type key
  type 'a T
  exception UNDEF of key
  exception DUP of key
  exception DUPS of key list
  val empty: 'a T
  val keys: 'a T -> key list
  val map_nodes: ('a -> 'b) -> 'a T -> 'b T
  val get_node: 'a T -> key -> 'a
  val map_node: key -> ('a -> 'a) -> 'a T -> 'a T
  val imm_preds: 'a T -> key -> key list
  val imm_succs: 'a T -> key -> key list
  val all_preds: 'a T -> key list -> key list
  val all_succs: 'a T -> key list -> key list
  val find_paths: 'a T -> key * key -> key list list
  val new_node: key * 'a -> 'a T -> 'a T
  val del_nodes: key list -> 'a T -> 'a T
  val edges: 'a T -> (key * key) list
  val add_edge: key * key -> 'a T -> 'a T
  val del_edge: key * key -> 'a T -> 'a T
  exception CYCLES of key list list
  val add_edge_acyclic: key * key -> 'a T -> 'a T
  val add_deps_acyclic: key * key list -> 'a T -> 'a T
  val merge_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T
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

infix del_key;
fun xs del_key x = if x mem_key xs then gen_rem eq_key (xs, x) else xs;

infix del_keys;
val op del_keys = foldl (op del_key);


(* tables and sets of keys *)

structure Table = TableFun(Key);
type keys = unit Table.table;

val empty_keys = Table.empty: keys;

infix mem_keys;
fun x mem_keys tab = is_some (Table.lookup (tab: keys, x));

infix ins_keys;
fun x ins_keys tab = if x mem_keys tab then tab else Table.update ((x, ()), tab);


(* graphs *)

datatype 'a T = Graph of ('a * (key list * key list)) Table.table;

exception UNDEF of key;
exception DUP = Table.DUP;
exception DUPS = Table.DUPS;

val empty = Graph Table.empty;
fun keys (Graph tab) = Table.keys tab;

fun get_entry (Graph tab) x =
  (case Table.lookup (tab, x) of
    Some entry => entry
  | None => raise UNDEF x);

fun map_entry x f (G as Graph tab) = Graph (Table.update ((x, f (get_entry G x)), tab));


(* nodes *)

fun map_nodes f (Graph tab) = Graph (Table.map (fn (i, ps) => (f i, ps)) tab);

fun get_node G = #1 o get_entry G;
fun map_node x f = map_entry x (fn (i, ps) => (f i, ps));


(* reachability *)

(*nodes reachable from xs -- topologically sorted for acyclic graphs*)
fun reachable next xs =
  let
    fun reach ((rs, R), x) =
      if x mem_keys R then (rs, R)
      else apfst (cons x) (reachs ((rs, x ins_keys R), next x))
    and reachs R_xs = foldl reach R_xs;
  in reachs (([], empty_keys), xs) end;

(*immediate*)
fun imm_preds G = #1 o #2 o get_entry G;
fun imm_succs G = #2 o #2 o get_entry G;

(*transitive*)
fun all_preds G = #1 o reachable (imm_preds G);
fun all_succs G = #1 o reachable (imm_succs G);


(* paths *)

fun find_paths G (x, y) =
  let
    val (_, X) = reachable (imm_succs G) [x];
    fun paths ps p =
      if eq_key (p, x) then [p :: ps]
      else flat (map (paths (p :: ps))
        (filter (fn pp => pp mem_keys X andalso not (pp mem_key ps)) (imm_preds G p)));
  in get_entry G y; if y mem_keys X then (paths [] y) else [] end;


(* nodes *)

exception DUPLICATE of key;

fun new_node (x, info) (Graph tab) =
  Graph (Table.update_new ((x, (info, ([], []))), tab));

fun del_nodes xs (Graph tab) =
  let
    fun del (x, (i, (preds, succs))) =
      if x mem_key xs then None
      else Some (x, (i, (preds del_keys xs, succs del_keys xs)));
  in Graph (Table.make (mapfilter del (Table.dest tab))) end;


(* edges *)

fun edges (Graph tab) =
  flat (map (fn (x, (_, (_, succs))) => (map (pair x) succs)) (Table.dest tab));

fun add_edge (x, y) =
  map_entry x (fn (i, (preds, succs)) => (i, (preds, y ins_key succs))) o
   map_entry y (fn (i, (preds, succs)) => (i, (x ins_key preds, succs)));

fun del_edge (x, y) =
  map_entry x (fn (i, (preds, succs)) => (i, (preds, succs del_key y))) o
   map_entry y (fn (i, (preds, succs)) => (i, (preds del_key x, succs)));


exception CYCLES of key list list;

fun add_edge_acyclic (x, y) G =
  (case find_paths G (y, x) of
    [] => add_edge (x, y) G
  | cycles => raise CYCLES (map (cons x) cycles));

fun add_deps_acyclic (y, xs) G =
  foldl (fn (H, x) => add_edge_acyclic (x, y) H) (G, xs);


(* merge_acyclic *)

fun merge_acyclic eq (Graph tab1, G2 as Graph tab2) =
  foldl (fn (G, xy) => add_edge_acyclic xy G)
    (Graph (Table.merge (fn ((i1, _), (i2, _)) => eq (i1, i2)) (tab1, tab2)), edges G2);


end;


(*graphs indexed by strings*)
structure Graph = GraphFun(type key = string val ord = string_ord);
