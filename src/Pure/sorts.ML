(*  Title:      Pure/sorts.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Type classes and sorts.
*)

signature SORTS =
sig
  val str_of_sort: sort -> string
  val str_of_arity: string * sort list * sort -> string
  val eq_sort: sort * sort -> bool
  val mem_sort: sort * sort list -> bool
  val subset_sort: sort list * sort list -> bool
  val eq_set_sort: sort list * sort list -> bool
  val ins_sort: sort * sort list -> sort list
  val union_sort: sort list * sort list -> sort list
  val rems_sort: sort list * sort list -> sort list
  type classes
  type arities
  val class_eq: classes -> class * class -> bool
  val class_less: classes -> class * class -> bool
  val class_le: classes -> class * class -> bool
  val sort_eq: classes -> sort * sort -> bool
  val sort_less: classes -> sort * sort -> bool
  val sort_le: classes -> sort * sort -> bool
  val sorts_le: classes -> sort list * sort list -> bool
  val inter_class: classes -> class * sort -> sort
  val inter_sort: classes -> sort * sort -> sort
  val norm_sort: classes -> sort -> sort
  val of_sort: classes * arities -> typ * sort -> bool
  exception DOMAIN of string * class
  val mg_domain: classes * arities -> string -> sort -> sort list  (*exception DOMAIN*)
  val witness_sorts: classes * arities -> string list
    -> sort list -> sort list -> (typ * sort) list
end;

structure Sorts: SORTS =
struct

(** type classes and sorts **)

(*
  Classes denote (possibly empty) collections of types that are
  partially ordered by class inclusion. They are represented
  symbolically by strings.

  Sorts are intersections of finitely many classes. They are
  represented by lists of classes.  Normal forms of sorts are sorted
  lists of minimal classes (wrt. current class inclusion).

  (types already defined in Pure/term.ML)
*)


(* simple printing -- lacks pretty printing, translations etc. *)

fun str_of_sort [c] = c
  | str_of_sort cs = Library.enclose "{" "}" (Library.commas cs);

fun str_of_arity (t, [], S) = t ^ " :: " ^ str_of_sort S
  | str_of_arity (t, Ss, S) = t ^ " :: " ^
      Library.enclose "(" ")" (Library.commas (map str_of_sort Ss)) ^ " " ^ str_of_sort S;


(* equality, membership and insertion of sorts *)

fun eq_sort ([]: sort, []) = true
  | eq_sort ((S1 :: Ss1), (S2 :: Ss2)) = S1 = S2 andalso eq_sort (Ss1, Ss2)
  | eq_sort (_, _) = false;

fun mem_sort (_: sort, []) = false
  | mem_sort (S, S' :: Ss) = eq_sort (S, S') orelse mem_sort (S, Ss);

fun ins_sort (S, Ss) = if mem_sort (S, Ss) then Ss else S :: Ss;

fun union_sort (Ss, []) = Ss
  | union_sort ([], Ss) = Ss
  | union_sort ((S :: Ss), Ss') = union_sort (Ss, ins_sort (S, Ss'));

fun subset_sort ([], Ss) = true
  | subset_sort (S :: Ss, Ss') = mem_sort (S, Ss') andalso subset_sort (Ss, Ss');

fun eq_set_sort (Ss, Ss') =
  Ss = Ss' orelse (subset_sort (Ss, Ss') andalso subset_sort (Ss', Ss));

val rems_sort = gen_rems eq_sort;


(* sort signature information *)

(*
  classes: graph representing class declarations together with proper
    subclass relation, which needs to be transitive and acyclic.

  arities: table of association lists of all type arities; (t, ars)
    means that type constructor t has the arities ars; an element (c,
    Ss) of ars represents the arity t::(Ss)c.  "Coregularity" of the
    arities structure requires that for any two declarations t:(Ss1)c1
    and t:(Ss2)c2 such that c1 <= c2 holds Ss1 <= Ss2.
*)

type classes = stamp Graph.T;
type arities = (class * sort list) list Symtab.table;



(** equality and inclusion **)

(* classes *)

fun class_eq (_: classes) (c1, c2:class) = c1 = c2;
val class_less: classes -> class * class -> bool = Graph.is_edge;
fun class_le classes (c1, c2) = c1 = c2 orelse class_less classes (c1, c2);


(* sorts *)

fun sort_le classes (S1, S2) =
  forall (fn c2 => exists  (fn c1 => class_le classes (c1, c2)) S1) S2;

fun sorts_le classes (Ss1, Ss2) =
  ListPair.all (sort_le classes) (Ss1, Ss2);

fun sort_eq classes (S1, S2) =
  sort_le classes (S1, S2) andalso sort_le classes (S2, S1);

fun sort_less classes (S1, S2) =
  sort_le classes (S1, S2) andalso not (sort_le classes (S2, S1));


(* normal forms of sorts *)

fun minimal_class classes S c =
  not (exists (fn c' => class_less classes (c', c)) S);

fun norm_sort classes S =
  sort_strings (distinct (filter (minimal_class classes S) S));



(** intersection **)

(*intersect class with sort (preserves minimality)*)
fun inter_class classes (c, S) =
  let
    fun intr [] = [c]
      | intr (S' as c' :: c's) =
          if class_le classes (c', c) then S'
          else if class_le classes (c, c') then intr c's
          else c' :: intr c's
  in intr S end;

(*instersect sorts (preserves minimality)*)
fun inter_sort classes = sort_strings o foldr (inter_class classes);



(** sorts of types **)

(* mg_domain *)

exception DOMAIN of string * class;

fun mg_domain _ _ [] = sys_error "mg_domain"  (*don't know number of args!*)
  | mg_domain (classes, arities) a S =
      let
        fun mg_dom c =
          (case Library.assoc_string (Symtab.lookup_multi (arities, a), c) of
            None => raise DOMAIN (a, c)
          | Some Ss => Ss);
        val doms = map mg_dom S;
      in foldl (ListPair.map (inter_sort classes)) (hd doms, tl doms) end;


(* of_sort *)

fun of_sort (classes, arities) =
  let
    fun ofS (_, []) = true
      | ofS (TFree (_, S), S') = sort_le classes (S, S')
      | ofS (TVar (_, S), S') = sort_le classes (S, S')
      | ofS (Type (a, Ts), S) =
          let val Ss = mg_domain (classes, arities) a S in
            ListPair.all ofS (Ts, Ss)
          end handle DOMAIN _ => false;
  in ofS end;



(** witness_sorts **)

fun witness_sorts_aux (classes, arities) log_types hyps sorts =
  let
    val top_witn = (propT, []);
    fun le S1 S2 = sort_le classes (S1, S2);
    fun get_solved S2 (T, S1) = if le S1 S2 then Some (T, S2) else None;
    fun get_hyp S2 S1 = if le S1 S2 then Some (TFree ("'hyp", S1), S2) else None;
    fun mg_dom t S = Some (mg_domain (classes, arities) t S) handle DOMAIN _ => None;

    fun witn_sort _ (solved_failed, []) = (solved_failed, Some top_witn)
      | witn_sort path ((solved, failed), S) =
          if exists (le S) failed then ((solved, failed), None)
          else
            (case get_first (get_solved S) solved of
              Some w => ((solved, failed), Some w)
            | None =>
                (case get_first (get_hyp S) hyps of
                  Some w => ((w :: solved, failed), Some w)
                | None => witn_types path log_types ((solved, failed), S)))

    and witn_sorts path x = foldl_map (witn_sort path) x

    and witn_types _ [] ((solved, failed), S) = ((solved, S :: failed), None)
      | witn_types path (t :: ts) (solved_failed, S) =
          (case mg_dom t S of
            Some SS =>
              (*do not descend into stronger args (achieving termination)*)
              if exists (fn D => le D S orelse exists (le D) path) SS then
                witn_types path ts (solved_failed, S)
              else
                let val ((solved', failed'), ws) = witn_sorts (S :: path) (solved_failed, SS) in
                  if forall is_some ws then
                    let val w = (Type (t, map (#1 o the) ws), S)
                    in ((w :: solved', failed'), Some w) end
                  else witn_types path ts ((solved', failed'), S)
                end
          | None => witn_types path ts (solved_failed, S));

  in witn_sorts [] (([], []), sorts) end;


fun witness_sorts (classes, arities) log_types hyps sorts =
  let
    (*double check result of witness search*)
    fun check_result None = None
      | check_result (Some (T, S)) =
          if of_sort (classes, arities) (T, S) then Some (T, S)
          else sys_error ("Sorts.witness_sorts: bad witness for sort " ^ str_of_sort S);
  in mapfilter check_result (#2 (witness_sorts_aux (classes, arities) log_types hyps sorts)) end;


end;
