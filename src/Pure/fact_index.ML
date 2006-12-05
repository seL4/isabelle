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
  val props: T -> thm list
  val could_unify: T -> term -> thm list
  val empty: T
  val add_local: bool -> bool -> (string * thm list) -> T -> T
  val add_global: (string * thm list) -> T -> T
  val find: T -> spec -> (string * thm list) list
end;

structure FactIndex: FACT_INDEX =
struct


(* indexing items *)

type spec = string list * string list;

val add_consts = fold_aterms
  (fn Const (c, _) => if c = Term.dummy_patternN then I else insert (op =) c | _ => I);

val add_frees = fold_aterms (fn Free (x, _) => insert (op =) x | _ => I);

fun index_term t (cs, xs) = (add_consts t cs, add_frees t xs);

fun index_thm th =
  let val {tpairs, hyps, prop, ...} = Thm.rep_thm th in
    index_term prop
    #> fold index_term hyps
    #> fold (fn (t, u) => index_term t #> index_term u) tpairs
  end;


(* build index *)

type fact = string * thm list;

datatype T = Index of
 {facts: fact list,
  consts: (serial * fact) list Symtab.table,
  frees: (serial * fact) list Symtab.table,
  props: thm Net.net};

fun facts (Index {facts, ...}) = facts;
fun props (Index {props, ...}) =
  sort_distinct (Term.term_ord o pairself Thm.full_prop_of) (Net.content props);
fun could_unify (Index {props, ...}) = Net.unify_term props;

val empty =
  Index {facts = [], consts = Symtab.empty, frees = Symtab.empty, props = Net.empty};

fun add_local do_props do_index (fact as (_, ths)) (Index {facts, consts, frees, props}) =
  let
    val entry = (serial (), fact);
    val (cs, xs) = fold index_thm ths ([], []);

    val (facts', consts', frees') =
      if do_index then
       (fact :: facts,
        consts |> fold (fn c => Symtab.update_list (c, entry)) cs,
        frees |> fold (fn x => Symtab.update_list (x, entry)) xs)
      else (facts, consts, frees);
    val props' =
      if do_props then props |> fold (fn th => Net.insert_term (K false) (Thm.prop_of th, th)) ths
      else props;
  in Index {facts = facts', consts = consts', frees = frees', props = props'} end;

val add_global = add_local false true;


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
      (map (Symtab.lookup_list consts) cs @
        map (Symtab.lookup_list frees) xs) |> intersects |> map #2;

end

end;
