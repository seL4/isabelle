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
  val empty: 'a T
  val get_nodes: 'a T -> (key * 'a) list
  val map_nodes: ('a -> 'b) -> 'a T -> 'b T
  val get_node: 'a T -> key -> 'a
  val map_node: key -> ('a -> 'a) -> 'a T -> 'a T
  val imm_preds: 'a T -> key -> key list
  val imm_succs: 'a T -> key -> key list
  val all_preds: 'a T -> key list -> key list
  val all_succs: 'a T -> key list -> key list
  val find_paths: 'a T -> key * key -> key list list
  exception DUPLICATE of key
  val add_node: key * 'a -> 'a T -> 'a T
  val add_edge: key * key -> 'a T -> 'a T
  exception CYCLES of key list list
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

val empty_keys = Table.empty: keys;

infix mem_keys;
fun x mem_keys tab = is_some (Table.lookup (tab: keys, x));

infix ins_keys;
fun x ins_keys tab = if x mem_keys tab then tab else Table.update ((x, ()), tab);

fun dest_keys tab = rev (Table.foldl (fn (xs, (x, ())) => x :: xs) ([], tab: keys));


(* graphs *)

datatype 'a T = Graph of ('a * (key list * key list)) Table.table;

exception UNDEFINED of key;

val empty = Graph Table.empty;

fun get_entry (Graph tab) x =
  (case Table.lookup (tab, x) of
    Some entry => entry
  | None => raise UNDEFINED x);

fun map_entry x f (G as Graph tab) = Graph (Table.update ((x, f (get_entry G x)), tab));


(* nodes *)

fun get_nodes (Graph tab) =
  rev (Table.foldl (fn (nodes, (x, (i, _))) => (x, i) :: nodes) ([], tab));

fun map_nodes f (Graph tab) = Graph (Table.map (fn (i, ps) => (f i, ps)) tab);

fun get_node G = #1 o get_entry G;
fun map_node x f = map_entry x (fn (i, ps) => (f i, ps));


(* reachability *)

fun reachable next xs =
  let
    fun reach (R, x) =
      if x mem_keys R then R
      else reachs (x ins_keys R, next x)
    and reachs R_xs = foldl reach R_xs;
  in reachs (empty_keys, xs) end;

(*immediate*)
fun imm_preds G = #1 o #2 o get_entry G;
fun imm_succs G = #2 o #2 o get_entry G;

(*transitive*)
fun all_preds G = dest_keys o reachable (imm_preds G);
fun all_succs G = dest_keys o reachable (imm_succs G);


(* paths *)

fun find_paths G (x, y) =
  let
    val X = reachable (imm_succs G) [x];
    fun paths ps p =
      if eq_key (p, x) then [p :: ps]
      else flat (map (paths (p :: ps))
        (filter (fn pp => pp mem_keys X andalso not (pp mem_key ps)) (imm_preds G p)));
  in get_entry G y; if y mem_keys X then (paths [] y) else [] end;


(* build graphs *)

exception DUPLICATE of key;

fun add_node (x, info) (Graph tab) =
  Graph (Table.update_new ((x, (info, ([], []))), tab)
    handle Table.DUP key => raise DUPLICATE key);

fun add_edge (x, y) G =
  G |> map_entry x (fn (i, (preds, succs)) => (i, (preds, y ins_key succs)))
    |> map_entry y (fn (i, (preds, succs)) => (i, (x ins_key preds, succs)));

exception CYCLES of key list list;

fun add_edge_acyclic (x, y) G =
  (case find_paths G (y, x) of
    [] => add_edge (x, y) G
  | cycles => raise CYCLES (map (cons x) cycles));

fun derive_node (x, y) zs G =
  foldl (fn (H, z) => add_edge_acyclic (z, x) H) (add_node (x, y) G, zs);


end;


(*graphs indexed by strings*)
structure Graph = GraphFun(type key = string val ord = string_ord);
