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
  val dest: 'a T -> (key * key list) list
  val minimals: 'a T -> key list
  val maximals: 'a T -> key list
  val map_nodes: ('a -> 'b) -> 'a T -> 'b T
  val get_node: 'a T -> key -> 'a
  val map_node: key -> ('a -> 'a) -> 'a T -> 'a T
  val imm_preds: 'a T -> key -> key list
  val imm_succs: 'a T -> key -> key list
  val all_preds: 'a T -> key list -> key list
  val all_succs: 'a T -> key list -> key list
  val strong_conn: 'a T -> key list list
  val find_paths: 'a T -> key * key -> key list list
  val new_node: key * 'a -> 'a T -> 'a T
  val del_nodes: key list -> 'a T -> 'a T
  val is_edge: 'a T -> key * key -> bool
  val add_edge: key * key -> 'a T -> 'a T
  val del_edge: key * key -> 'a T -> 'a T
  val merge: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T
  exception CYCLES of key list list
  val add_edge_acyclic: key * key -> 'a T -> 'a T
  val add_deps_acyclic: key * key list -> 'a T -> 'a T
  val merge_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T
  val add_edge_trans_acyclic: key * key -> 'a T -> 'a T
  val merge_trans_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T
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
fun dest (Graph tab) = map (fn (x, (_, (_, succs))) => (x, succs)) (Table.dest tab);

fun minimals (Graph tab) =
  Table.foldl (fn (ms, (m, (_, ([], _)))) => m :: ms | (ms, _) => ms) ([], tab);
fun maximals (Graph tab) =
  Table.foldl (fn (ms, (m, (_, (_, [])))) => m :: ms | (ms, _) => ms) ([], tab);

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
    fun reach ((R, rs), x) =
      if x mem_keys R then (R, rs)
      else apsnd (cons x) (reachs ((x ins_keys R, rs), next x))
    and reachs R_xs = foldl reach R_xs;
  in foldl_map (reach o apfst (rpair [])) (empty_keys, xs) end;

(*immediate*)
fun imm_preds G = #1 o #2 o get_entry G;
fun imm_succs G = #2 o #2 o get_entry G;

(*transitive*)
fun all_preds G = flat o snd o reachable (imm_preds G);
fun all_succs G = flat o snd o reachable (imm_succs G);

(*strongly connected components; see: David King and John Launchbury,
  "Structuring Depth First Search Algorithms in Haskell"*)
fun strong_conn G = filter_out null (snd (reachable (imm_preds G)
  (flat (rev (snd (reachable (imm_succs G) (keys G)))))));


(* paths *)

fun find_paths G (x, y) =
  let
    val (X, _) = reachable (imm_succs G) [x];
    fun paths ps p =
      if not (null ps) andalso eq_key (p, x) then [p :: ps]
      else if p mem_keys X andalso not (p mem_key ps)
      then flat (map (paths (p :: ps)) (imm_preds G p))
      else [];
  in paths [] y end;


(* nodes *)

exception DUPLICATE of key;

fun new_node (x, info) (Graph tab) =
  Graph (Table.update_new ((x, (info, ([], []))), tab));

fun del_nodes xs (Graph tab) =
  let
    fun del (x, (i, (preds, succs))) =
      if x mem_key xs then None
      else Some (x, (i, (foldl op del_key (preds, xs), foldl op del_key (succs, xs))));
  in Graph (Table.make (mapfilter del (Table.dest tab))) end;


(* edges *)

fun is_edge G (x, y) = y mem_key imm_succs G x handle UNDEF _ => false;

fun add_edge (x, y) G =
  if is_edge G (x, y) then G
  else
    G |> map_entry y (fn (i, (preds, succs)) => (i, (x :: preds, succs)))
      |> map_entry x (fn (i, (preds, succs)) => (i, (preds, y :: succs)));

fun del_edge (x, y) G =
  if is_edge G (x, y) then
    G |> map_entry y (fn (i, (preds, succs)) => (i, (preds del_key x, succs)))
      |> map_entry x (fn (i, (preds, succs)) => (i, (preds, succs del_key y)))
  else G;

fun diff_edges G1 G2 =
  flat (dest G1 |> map (fn (x, ys) => ys |> mapfilter (fn y =>
    if is_edge G2 (x, y) then None else Some (x, y))));

fun edges G = diff_edges G empty;


(* merge *)

fun gen_merge add eq (Graph tab1, G2 as Graph tab2) =
  let
    fun eq_node ((i1, _), (i2, _)) = eq (i1, i2);
    fun no_edges (i, _) = (i, ([], []));
  in fold add (edges G2) (Graph (Table.merge eq_node (tab1, Table.map no_edges tab2))) end;

fun merge eq GG = gen_merge add_edge eq GG;


(* maintain acyclic graphs *)

exception CYCLES of key list list;

fun add_edge_acyclic (x, y) G =
  if is_edge G (x, y) then G
  else
    (case find_paths G (y, x) of
      [] => add_edge (x, y) G
    | cycles => raise CYCLES (map (cons x) cycles));

fun add_deps_acyclic (y, xs) G =
  foldl (fn (H, x) => add_edge_acyclic (x, y) H) (G, xs);

fun merge_acyclic eq GG = gen_merge add_edge_acyclic eq GG;


(* maintain transitive acyclic graphs *)

fun add_edge_trans_acyclic (x, y) G =
  add_edge_acyclic (x, y) G |>
  fold add_edge (Library.product (all_preds G [x]) (all_succs G [y]));

fun merge_trans_acyclic eq (G1, G2) =
  merge_acyclic eq (G1, G2) |>
  fold add_edge_trans_acyclic (diff_edges G1 G2 @ diff_edges G2 G1);

end;


(*graphs indexed by strings*)
structure Graph = GraphFun(type key = string val ord = string_ord);
