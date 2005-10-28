(*  Title:      Pure/fact_index.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Facts indexed by consts or frees.
*)

signature FACT_INDEX =
sig
  type spec
  type T
  val facts: T -> (string * thm list) list
  val could_unify: T -> term -> thm list
  val empty: T
  val add_global: (string * thm list) -> T -> T
  val add_local: (string -> bool) -> (string * thm list) -> T -> T
  val find: T -> spec -> (string * thm list) list
end;

structure FactIndex: FACT_INDEX =
struct


(* indexing items *)

type spec = string list * string list;

val add_consts = fold_aterms
  (fn Const (c, _) => if c = Term.dummy_patternN then I else insert (op =) c | _ => I);

fun add_frees known = fold_aterms
  (fn Free (x, _) => if known x then insert (op =) x else I | _ => I);

fun index_term known t (cs, xs) = (add_consts t cs, add_frees known t xs);

fun index_thm known th idx =
  let val {tpairs, hyps, prop, ...} = Thm.rep_thm th in
    idx
    |> index_term known prop
    |> fold (index_term known) hyps
    |> fold (fn (t, u) => index_term known t #> index_term known u) tpairs
  end;


(* build index *)

type fact = string * thm list;

datatype T = Index of
 {facts: fact list,
  consts: (serial * fact) list Symtab.table,
  frees: (serial * fact) list Symtab.table,
  props: thm Net.net};

fun facts (Index {facts, ...}) = facts;
fun could_unify (Index {props, ...}) = Net.unify_term props;

val empty =
  Index {facts = [], consts = Symtab.empty, frees = Symtab.empty, props = Net.empty};

fun add do_props known (fact as (_, ths)) (Index {facts, consts, frees, props}) =
  let
    val entry = (serial (), fact);
    val (cs, xs) = fold (index_thm known) ths ([], []);

    val facts' = fact :: facts;
    val consts' = consts |> fold (fn c => Symtab.update_multi (c, entry)) cs;
    val frees' = frees |> fold (fn x => Symtab.update_multi (x, entry)) xs;
    val props' = props |> K do_props ?
      fold (fn th => Net.insert_term (K false) (Thm.prop_of th, th)) ths;
  in Index {facts = facts', consts = consts', frees = frees', props = props'} end;

val add_global = add false (K false);
val add_local = add true;


(* find by consts/frees *)

local

fun fact_ord ((i, _), (j, _)) = int_ord (j, i);

fun intersects [xs] = xs
  | intersects xss =
      if exists null xss then []
      else fold (OrdList.inter fact_ord) (tl xss) (hd xss);

in

fun find idx ([], []) = facts idx
  | find (Index {consts, frees, ...}) (cs, xs) =
      (map (Symtab.lookup_multi consts) cs @
        map (Symtab.lookup_multi frees) xs) |> intersects |> map #2;

end

end;
