(*  Title:      Pure/fact_index.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Facts indexed by consts or (some) frees.
*)

signature FACT_INDEX =
sig
  val index_term: (string -> bool) -> (string list * string list) * term
    -> string list * string list
  val index_thm: (string -> bool) -> (string list * string list) * thm
    -> string list * string list
  type T
  val empty: T
  val add: (string -> bool) -> T * (string * thm list) -> T
  val find: string list * string list -> T -> (string * thm list) list
end;

structure FactIndex: FACT_INDEX =
struct

(* indexing items *)

fun add_frees pred (Free (x, _), xs) = if pred x then x ins_string xs else xs
  | add_frees pred (t $ u, xs) = add_frees pred (t, add_frees pred (u, xs))
  | add_frees pred (Abs (_, _, t), xs) = add_frees pred (t, xs)
  | add_frees _ (_, xs) = xs;

fun index_term pred ((cs, xs), t) =
  (Term.add_term_consts (t, cs) \ Term.dummy_patternN, add_frees pred (t, xs));

fun index_thm pred (idx, th) =
  let val {hyps, prop, ...} = Thm.rep_thm th
  in foldl (index_term pred) (index_term pred (idx, prop), hyps) end;


(* build index *)

datatype T = Index of {next: int, facts: (string * thm list) list,
  consts: (int * (string * thm list)) list Symtab.table,
  frees: (int * (string * thm list)) list Symtab.table};

val empty =
  Index {next = 0, facts = [], consts = Symtab.empty, frees = Symtab.empty};

fun add pred (Index {next, facts, consts, frees}, (name, ths)) =
  let
    fun upd (tab, a) = Symtab.update_multi ((a, (next, (name, ths))), tab);
    val (cs, xs) = foldl (index_thm pred) (([], []), ths);
  in
    Index {next = next + 1, facts = (name, ths) :: facts,
      consts = foldl upd (consts, cs), frees = foldl upd (frees, xs)}
  end;


(* find facts *)

fun intersect ([], _) = []
  | intersect (_, []) = []
  | intersect (xxs as ((x as (i: int, _)) :: xs), yys as ((y as (j, _)) :: ys)) =
      if i = j then x :: intersect (xs, ys)
      else if i > j then intersect (xs, yys)
      else intersect (xxs, ys);

fun intersects [xs] = xs
  | intersects xss = if exists null xss then [] else foldl intersect (hd xss, tl xss);

fun find ([], []) (Index {facts, ...}) = facts
  | find (cs, xs) (Index {consts, frees, ...}) =
      (map (curry Symtab.lookup_multi consts) cs @
        map (curry Symtab.lookup_multi frees) xs) |> intersects |> map #2;

end;
