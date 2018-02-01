(*  Title:      Tools/Argo/argo_heap.ML
    Author:     Sascha Boehme

A maximum-priority heap for literals with integer priorities and with inverse indices.
The heap is intended to be used as VSIDS-like decision heuristics. This implementation
is based on pairing heaps described in:

  Chris Okasaki. Purely Functional Data Structures. Chapter 5.
  Cambridge University Press, 1998.
*)

signature ARGO_HEAP =
sig
  type heap
  val heap: heap
  val insert: Argo_Lit.literal -> heap -> heap
  val extract: heap -> (Argo_Lit.literal * heap) option
  val increase: Argo_Lit.literal -> heap -> heap
  val count: Argo_Lit.literal -> heap -> heap
  val decay: heap -> heap
  val rebuild: (Argo_Term.term -> bool) -> heap -> heap
end

structure Argo_Heap: ARGO_HEAP =
struct

(* heuristic activity constants *)

val min_incr = 128
fun decay_incr i = (i * 11) div 10
val max_activity = Integer.pow 24 2
val activity_rescale = Integer.pow 14 2


(* data structures and basic operations *)

datatype tree = E | T of Argo_Term.term * bool * tree list

datatype parent = None | Root | Some of Argo_Term.term

type heap = {
  incr: int, (* the increment to apply in an increase operation *)
  vals: ((int * int) * parent) Argo_Termtab.table, (* weights and parents of the stored terms *)
  tree: tree} (* the pairing heap of literals; note: the tree caches literal polarities *)

fun mk_heap incr vals tree: heap = {incr=incr, vals=vals, tree=tree}
fun mk_heap' incr (tree, vals) = mk_heap incr vals tree

val heap = mk_heap min_incr Argo_Termtab.empty E

val empty_value = ((0, 0), None)
fun value_of vals t = the_default empty_value (Argo_Termtab.lookup vals t)
fun map_value t = Argo_Termtab.map_default (t, empty_value)


(* weight operations *)

(*
  The weight of a term is a pair of activity and count. The activity describes how
  often a term participated in conflicts. The count describes how often a term occurs
  in clauses.
*)

val weight_ord = prod_ord int_ord int_ord

fun weight_of vals t = fst (value_of vals t)

fun less_than vals t1 t2 = is_less (weight_ord (weight_of vals t1, weight_of vals t2))

fun rescale activity = activity div activity_rescale

fun incr_activity incr t = map_value t (apfst (apfst (Integer.add incr)))
fun incr_count t = map_value t (apfst (apsnd (Integer.add 1)))

fun rescale_activities a incr vals =
  if a <= max_activity then (incr, vals)
  else (rescale incr, Argo_Termtab.map (fn _ => apfst (apfst rescale)) vals)


(* reverse index operations *)

(*
  The reverse index is required to retrieve elements when increasing their priorities.
*)

fun contains vals t =
  (case value_of vals t of
    (_, None) => false
  | _ => true)

fun path_to vals t parents =
  (case value_of vals t of
    (_, Root) => parents
  | (_, Some parent) => path_to vals parent (t :: parents)
  | _ => raise Fail "bad heap")

fun put_parent t parent = map_value t (apsnd (K parent))
fun delete t = put_parent t None
fun root t = put_parent t Root

fun as_root (tree as T (t, _, _), vals) = (tree, root t vals)
  | as_root x = x


(* pairing heap operations *)

fun merge E tree vals = (tree, vals)
  | merge tree E vals = (tree, vals)
  | merge (tree1 as T (t1, p1, trees1)) (tree2 as T (t2, p2, trees2)) vals =
      if less_than vals t1 t2 then (T (t2, p2, tree1 :: trees2), put_parent t1 (Some t2) vals)
      else (T (t1, p1, tree2 :: trees1), put_parent t2 (Some t1) vals)

fun merge_pairs [] vals = (E, vals)
  | merge_pairs [tree] vals = (tree, vals)
  | merge_pairs (tree1 :: tree2 :: trees) vals =
      vals |> merge tree1 tree2 ||>> merge_pairs trees |-> uncurry merge


(* cutting subtrees specified by a path *)

(*
  The extractions are performed in such a way that the heap is changed in as few positions
  as possible.
*)

fun with_index f u ((tree as T (t, _, _)) :: trees) =
      if Argo_Term.eq_term (t, u) then f tree ||> (fn E => trees | tree => tree :: trees)
      else with_index f u trees ||> cons tree
  | with_index _ _ _ = raise Fail "bad heap"

fun lift_index f u (T (t, p, trees)) = with_index f u trees ||> (fn trees => T (t, p, trees))
  | lift_index _ _ E = raise Fail "bad heap"

fun cut t [] tree = lift_index (fn tree => (tree, E)) t tree
  | cut t (parent :: ts) tree = lift_index (cut t ts) parent tree


(* filtering the heap *)

val proper_trees = filter (fn E => false | T _ => true)

fun filter_tree _ E vals = (E, vals)
  | filter_tree pred (T (t, p, ts)) vals =
      let val (ts, vals) = fold_map (filter_tree pred) ts vals |>> proper_trees
      in if pred t then (T (t, p, ts), vals) else merge_pairs ts (delete t vals) end


(* exported heap operations *)

fun insert lit (h as {incr, vals, tree}: heap) = 
  let val (t, p) = Argo_Lit.dest lit
  in if contains vals t then h else mk_heap' incr (merge tree (T (t, p, [])) (root t vals)) end

fun extract ({tree=E, ...}: heap) = NONE
  | extract ({incr, vals, tree=T (t, p, ts)}: heap) =
      SOME (Argo_Lit.literal t p, mk_heap' incr (as_root (merge_pairs ts (delete t vals))))

fun with_term lit f = f (Argo_Lit.term_of lit)

(*
  If the changed weight violates the heap property, the corresponding tree
  is extracted and merged with the root.
*)

fun fix t (w, Some parent) (incr, vals) tree =
      if is_less (weight_ord (weight_of vals parent, w)) then
        let val (tree1, tree2) = cut t (path_to vals parent []) tree
        in mk_heap' incr (merge tree1 tree2 (root t vals)) end
      else mk_heap incr vals tree
  | fix _ _ (incr, vals) tree = mk_heap incr vals tree

fun increase lit ({incr, vals, tree}: heap) = with_term lit (fn t =>
  let
    val vals = incr_activity incr t vals
    val value as ((a, _), _) = value_of vals t
  in fix t value (rescale_activities a incr vals) tree end)

fun count lit ({incr, vals, tree}: heap) = with_term lit (fn t =>
  let val vals = incr_count t vals
  in fix t (value_of vals t) (incr, vals) tree end)

fun decay ({incr, vals, tree}: heap) = mk_heap (decay_incr incr) vals tree

fun rebuild pred ({incr, vals, tree}: heap) = mk_heap' incr (filter_tree pred tree vals)

end
