(*  Title:      Pure/fact_index.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Facts indexed by consts or frees.
*)

signature FACT_INDEX =
sig
  type spec
  val index_term: (string -> bool) -> term -> spec -> spec
  val index_thm: (string -> bool) -> thm -> spec -> spec
  type T
  val facts: T -> (string * thm list) list
  val empty: T
  val add: (string -> bool) -> (string * thm list) -> T -> T
  val find: T -> spec -> (string * thm list) list
end;

structure FactIndex: FACT_INDEX =
struct

type spec = string list * string list;


(* indexing items *)

val add_consts = fold_aterms
  (fn Const (c, _) => if c = Term.dummy_patternN then I else insert (op =) c | _ => I);

fun add_frees pred = fold_aterms
  (fn Free (x, _) => if pred x then insert (op =) x else I | _ => I);

fun index_term pred t (cs, xs) = (add_consts t cs, add_frees pred t xs);

fun index_thm pred th idx =
  let val {tpairs, hyps, prop, ...} = Thm.rep_thm th in
    idx
    |> index_term pred prop
    |> fold (index_term pred) hyps
    |> fold (fn (t, u) => index_term pred t #> index_term pred u) tpairs
  end;


(* build index *)

datatype T = Index of {next: int, facts: (string * thm list) list,
  consts: (int * (string * thm list)) list Symtab.table,
  frees: (int * (string * thm list)) list Symtab.table};

fun facts (Index {facts, ...}) = facts;

val empty =
  Index {next = 0, facts = [], consts = Symtab.empty, frees = Symtab.empty};

fun add pred (name, ths) (Index {next, facts, consts, frees}) =
  let
    fun upd a = Symtab.curried_update_multi (a, (next, (name, ths)));
    val (cs, xs) = fold (index_thm pred) ths ([], []);
  in
    Index {next = next + 1, facts = (name, ths) :: facts,
      consts = fold upd cs consts, frees = fold upd xs frees}
  end;


(* find facts *)

fun fact_ord ((i, _), (j, _)) = int_ord (j, i);

fun intersects [xs] = xs
  | intersects xss =
      if exists null xss then []
      else fold (OrdList.inter fact_ord) (tl xss) (hd xss);

fun find idx ([], []) = facts idx
  | find (Index {consts, frees, ...}) (cs, xs) =
      (map (Symtab.curried_lookup_multi consts) cs @
        map (Symtab.curried_lookup_multi frees) xs) |> intersects |> map #2;

end;
