(*  Title:      Pure/General/graph.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

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
  val get_node: 'a T -> key -> 'a                                     (*exception UNDEF*)
  val map_node: key -> ('a -> 'a) -> 'a T -> 'a T
  val imm_preds: 'a T -> key -> key list
  val imm_succs: 'a T -> key -> key list
  val all_preds: 'a T -> key list -> key list
  val all_succs: 'a T -> key list -> key list
  val strong_conn: 'a T -> key list list
  val find_paths: 'a T -> key * key -> key list list
  val new_node: key * 'a -> 'a T -> 'a T                              (*exception DUP*)
  val default_node: key * 'a -> 'a T -> 'a T
  val del_nodes: key list -> 'a T -> 'a T                             (*exception UNDEF*)
  val is_edge: 'a T -> key * key -> bool
  val add_edge: key * key -> 'a T -> 'a T
  val del_edge: key * key -> 'a T -> 'a T
  val merge: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T                 (*exception DUPS*)
  exception CYCLES of key list list
  val add_edge_acyclic: key * key -> 'a T -> 'a T                     (*exception CYCLES*)
  val add_deps_acyclic: key * key list -> 'a T -> 'a T                (*exception CYCLES*)
  val merge_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T         (*exception CYCLES*)
  val add_edge_trans_acyclic: key * key -> 'a T -> 'a T               (*exception CYCLES*)
  val merge_trans_acyclic: ('a * 'a -> bool) -> 'a T * 'a T -> 'a T   (*exception CYCLES*)
end;

functor GraphFun(Key: KEY): GRAPH =
struct

(* keys *)

type key = Key.key;

val eq_key = equal EQUAL o Key.ord;

infix mem_key;
val op mem_key = gen_mem eq_key;

val remove_key = remove eq_key;


(* tables and sets of keys *)

structure Table = TableFun(Key);
type keys = unit Table.table;

val empty_keys = Table.empty: keys;

infix mem_keys;
fun x mem_keys tab = Table.defined (tab: keys) x;

infix ins_keys;
fun x ins_keys tab = Table.insert (K true) (x, ()) (tab: keys);


(* graphs *)

datatype 'a T = Graph of ('a * (key list * key list)) Table.table;

exception UNDEF of key;
exception DUP = Table.DUP;
exception DUPS = Table.DUPS;

val empty = Graph Table.empty;
fun keys (Graph tab) = Table.keys tab;
fun dest (Graph tab) = map (fn (x, (_, (_, succs))) => (x, succs)) (Table.dest tab);

fun minimals (Graph tab) = Table.fold (fn (m, (_, ([], _))) => cons m | _ => I) tab [];
fun maximals (Graph tab) = Table.fold (fn (m, (_, (_, []))) => cons m | _ => I) tab [];

fun get_entry (Graph tab) x =
  (case Table.lookup (tab, x) of
    SOME entry => entry
  | NONE => raise UNDEF x);

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
    and reachs R_xs = Library.foldl reach R_xs;
  in foldl_map (reach o apfst (rpair [])) (empty_keys, xs) end;

(*immediate*)
fun imm_preds G = #1 o #2 o get_entry G;
fun imm_succs G = #2 o #2 o get_entry G;

(*transitive*)
fun all_preds G = List.concat o snd o reachable (imm_preds G);
fun all_succs G = List.concat o snd o reachable (imm_succs G);

(*strongly connected components; see: David King and John Launchbury,
  "Structuring Depth First Search Algorithms in Haskell"*)
fun strong_conn G = filter_out null (snd (reachable (imm_preds G)
  (List.concat (rev (snd (reachable (imm_succs G) (keys G)))))));


(* paths *)

fun find_paths G (x, y) =
  let
    val (X, _) = reachable (imm_succs G) [x];
    fun paths ps p =
      if not (null ps) andalso eq_key (p, x) then [p :: ps]
      else if p mem_keys X andalso not (p mem_key ps)
      then List.concat (map (paths (p :: ps)) (imm_preds G p))
      else [];
  in paths [] y end;


(* nodes *)

fun new_node (x, info) (Graph tab) =
  Graph (Table.update_new ((x, (info, ([], []))), tab));

fun default_node (x, info) (Graph tab) =
  Graph (Table.default (x, (info, ([], []))) tab);

fun del_nodes xs (Graph tab) =
  Graph (tab
    |> fold Table.delete xs
    |> Table.map (fn (i, (preds, succs)) =>
      (i, (fold remove_key xs preds, fold remove_key xs succs))));


(* edges *)

fun is_edge G (x, y) = y mem_key imm_succs G x handle UNDEF _ => false;

fun add_edge (x, y) G =
  if is_edge G (x, y) then G
  else
    G |> map_entry y (fn (i, (preds, succs)) => (i, (x :: preds, succs)))
      |> map_entry x (fn (i, (preds, succs)) => (i, (preds, y :: succs)));

fun del_edge (x, y) G =
  if is_edge G (x, y) then
    G |> map_entry y (fn (i, (preds, succs)) => (i, (remove_key x preds, succs)))
      |> map_entry x (fn (i, (preds, succs)) => (i, (preds, remove_key y succs)))
  else G;

fun diff_edges G1 G2 =
  List.concat (dest G1 |> map (fn (x, ys) => ys |> List.mapPartial (fn y =>
    if is_edge G2 (x, y) then NONE else SOME (x, y))));

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

fun add_deps_acyclic (y, xs) = fold (fn x => add_edge_acyclic (x, y)) xs;

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
structure Graph = GraphFun(type key = string val ord = fast_string_ord);
