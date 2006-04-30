(*  Title:      Pure/sorts.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

The order-sorted algebra of type classes.
*)

signature SORTS =
sig
  val eq_set: sort list * sort list -> bool
  val union: sort list -> sort list -> sort list
  val subtract: sort list -> sort list -> sort list
  val remove_sort: sort -> sort list -> sort list
  val insert_sort: sort -> sort list -> sort list
  val insert_typ: typ -> sort list -> sort list
  val insert_typs: typ list -> sort list -> sort list
  val insert_term: term -> sort list -> sort list
  val insert_terms: term list -> sort list -> sort list
  type classes
  type arities
  val class_eq: classes -> class * class -> bool
  val class_less: classes -> class * class -> bool
  val class_le: classes -> class * class -> bool
  val sort_eq: classes -> sort * sort -> bool
  val sort_le: classes -> sort * sort -> bool
  val sorts_le: classes -> sort list * sort list -> bool
  val inter_sort: classes -> sort * sort -> sort
  val norm_sort: classes -> sort -> sort
  val of_sort: classes * arities -> typ * sort -> bool
  exception DOMAIN of string * class
  val mg_domain: classes * arities -> string -> sort -> sort list  (*exception DOMAIN*)
  val witness_sorts: classes * arities -> string list ->
    sort list -> sort list -> (typ * sort) list
  val add_arities: Pretty.pp -> classes -> string * (class * sort list) list -> arities -> arities
  val rebuild_arities: Pretty.pp -> classes -> arities -> arities
  val merge_arities: Pretty.pp -> classes -> arities * arities -> arities
  val add_class: Pretty.pp -> class * class list -> classes -> classes
  val add_classrel: Pretty.pp -> class * class -> classes -> classes
  val merge_classes: Pretty.pp -> classes * classes -> classes
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
*)


(* ordered lists of sorts *)

val eq_set = OrdList.eq_set Term.sort_ord;
val op union = OrdList.union Term.sort_ord;
val subtract = OrdList.subtract Term.sort_ord;

val remove_sort = OrdList.remove Term.sort_ord;
val insert_sort = OrdList.insert Term.sort_ord;

fun insert_typ (TFree (_, S)) Ss = insert_sort S Ss
  | insert_typ (TVar (_, S)) Ss = insert_sort S Ss
  | insert_typ (Type (_, Ts)) Ss = insert_typs Ts Ss
and insert_typs [] Ss = Ss
  | insert_typs (T :: Ts) Ss = insert_typs Ts (insert_typ T Ss);

fun insert_term (Const (_, T)) Ss = insert_typ T Ss
  | insert_term (Free (_, T)) Ss = insert_typ T Ss
  | insert_term (Var (_, T)) Ss = insert_typ T Ss
  | insert_term (Bound _) Ss = Ss
  | insert_term (Abs (_, T, t)) Ss = insert_term t (insert_typ T Ss)
  | insert_term (t $ u) Ss = insert_term t (insert_term u Ss);

fun insert_terms [] Ss = Ss
  | insert_terms (t :: ts) Ss = insert_terms ts (insert_term t Ss);


(* sort signature information *)

(*
  classes: graph representing class declarations together with proper
    subclass relation, which needs to be transitive and acyclic.

  arities: table of association lists of all type arities; (t, ars)
    means that type constructor t has the arities ars; an element (c,
    Ss) of ars represents the arity t::(Ss)c.  "Coregularity" of the
    arities structure requires that for any two declarations
    t::(Ss1)c1 and t::(Ss2)c2 such that c1 <= c2 holds Ss1 <= Ss2.
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
  forall (fn c2 => exists (fn c1 => class_le classes (c1, c2)) S1) S2;

fun sorts_le classes (Ss1, Ss2) =
  ListPair.all (sort_le classes) (Ss1, Ss2);

fun sort_eq classes (S1, S2) =
  sort_le classes (S1, S2) andalso sort_le classes (S2, S1);


(* normal forms of sorts *)

fun minimal_class classes S c =
  not (exists (fn c' => class_less classes (c', c)) S);

fun norm_sort _ [] = []
  | norm_sort _ (S as [_]) = S
  | norm_sort classes S = sort_distinct string_ord (filter (minimal_class classes S) S);



(** intersection -- preserving minimality **)

fun inter_class classes c S =
  let
    fun intr [] = [c]
      | intr (S' as c' :: c's) =
          if class_le classes (c', c) then S'
          else if class_le classes (c, c') then intr c's
          else c' :: intr c's
  in intr S end;

fun inter_sort classes (S1, S2) =
  sort_strings (fold (inter_class classes) S1 S2);



(** sorts of types **)

(* mg_domain *)

exception DOMAIN of string * class;

fun mg_domain (classes, arities) a S =
  let
    fun dom c =
      (case AList.lookup (op =) (Symtab.lookup_list arities a) c of
        NONE => raise DOMAIN (a, c)
      | SOME Ss => Ss);
    fun dom_inter c Ss = ListPair.map (inter_sort classes) (dom c, Ss);
  in
    (case S of
      [] => sys_error "mg_domain"  (*don't know number of args!*)
    | c :: cs => fold dom_inter cs (dom c))
  end;


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

local

fun witness_aux (classes, arities) log_types hyps sorts =
  let
    val top_witn = (propT, []);
    fun le S1 S2 = sort_le classes (S1, S2);
    fun get_solved S2 (T, S1) = if le S1 S2 then SOME (T, S2) else NONE;
    fun get_hyp S2 S1 = if le S1 S2 then SOME (TFree ("'hyp", S1), S2) else NONE;
    fun mg_dom t S = SOME (mg_domain (classes, arities) t S) handle DOMAIN _ => NONE;

    fun witn_sort _ (solved_failed, []) = (solved_failed, SOME top_witn)
      | witn_sort path ((solved, failed), S) =
          if exists (le S) failed then ((solved, failed), NONE)
          else
            (case get_first (get_solved S) solved of
              SOME w => ((solved, failed), SOME w)
            | NONE =>
                (case get_first (get_hyp S) hyps of
                  SOME w => ((w :: solved, failed), SOME w)
                | NONE => witn_types path log_types ((solved, failed), S)))

    and witn_sorts path x = foldl_map (witn_sort path) x

    and witn_types _ [] ((solved, failed), S) = ((solved, S :: failed), NONE)
      | witn_types path (t :: ts) (solved_failed, S) =
          (case mg_dom t S of
            SOME SS =>
              (*do not descend into stronger args (achieving termination)*)
              if exists (fn D => le D S orelse exists (le D) path) SS then
                witn_types path ts (solved_failed, S)
              else
                let val ((solved', failed'), ws) = witn_sorts (S :: path) (solved_failed, SS) in
                  if forall is_some ws then
                    let val w = (Type (t, map (#1 o the) ws), S)
                    in ((w :: solved', failed'), SOME w) end
                  else witn_types path ts ((solved', failed'), S)
                end
          | NONE => witn_types path ts (solved_failed, S));

  in witn_sorts [] (([], []), sorts) end;

fun str_of_sort [c] = c
  | str_of_sort cs = enclose "{" "}" (commas cs);

in

fun witness_sorts (classes, arities) log_types hyps sorts =
  let
    (*double check result of witness construction*)
    fun check_result NONE = NONE
      | check_result (SOME (T, S)) =
          if of_sort (classes, arities) (T, S) then SOME (T, S)
          else sys_error ("Sorts.witness_sorts: bad witness for sort " ^ str_of_sort S);
  in map_filter check_result (#2 (witness_aux (classes, arities) log_types hyps sorts)) end;

end;



(** build sort algebras **)

(* classes *)

local

fun err_dup_classes cs =
  error ("Duplicate declaration of class(es): " ^ commas_quote cs);

fun err_cyclic_classes pp css =
  error (cat_lines (map (fn cs =>
    "Cycle in class relation: " ^ Pretty.string_of_classrel pp cs) css));

in

fun add_class pp (c, cs) classes =
  let
    val classes' = classes |> Graph.new_node (c, stamp ())
      handle Graph.DUP dup => err_dup_classes [dup];
    val classes'' = classes' |> fold Graph.add_edge_trans_acyclic (map (pair c) cs)
      handle Graph.CYCLES css => err_cyclic_classes pp css;
  in classes'' end;

fun add_classrel pp rel classes =
  classes |> Graph.add_edge_trans_acyclic rel
    handle Graph.CYCLES css => err_cyclic_classes pp css;

fun merge_classes pp args : classes =
  Graph.merge_trans_acyclic (op =) args
    handle Graph.DUPS cs => err_dup_classes cs
        | Graph.CYCLES css => err_cyclic_classes pp css;

end;


(* arities *)

local

fun for_classes _ NONE = ""
  | for_classes pp (SOME (c1, c2)) =
      " for classes " ^ Pretty.string_of_classrel pp [c1, c2];

fun err_conflict pp t cc (c, Ss) (c', Ss') =
  error ("Conflict of type arities" ^ for_classes pp cc ^ ":\n  " ^
    Pretty.string_of_arity pp (t, Ss, [c]) ^ " and\n  " ^
    Pretty.string_of_arity pp (t, Ss', [c']));

fun coregular pp C t (c, Ss) ars =
  let
    fun conflict (c', Ss') =
      if class_le C (c, c') andalso not (sorts_le C (Ss, Ss')) then
        SOME ((c, c'), (c', Ss'))
      else if class_le C (c', c) andalso not (sorts_le C (Ss', Ss)) then
        SOME ((c', c), (c', Ss'))
      else NONE;
  in
    (case get_first conflict ars of
      SOME ((c1, c2), (c', Ss')) => err_conflict pp t (SOME (c1, c2)) (c, Ss) (c', Ss')
    | NONE => (c, Ss) :: ars)
  end;

fun insert pp C t (c, Ss) ars =
  (case AList.lookup (op =) ars c of
    NONE => coregular pp C t (c, Ss) ars
  | SOME Ss' =>
      if sorts_le C (Ss, Ss') then ars
      else if sorts_le C (Ss', Ss)
      then coregular pp C t (c, Ss) (remove (op =) (c, Ss') ars)
      else err_conflict pp t NONE (c, Ss) (c, Ss'));

fun complete C (c, Ss) = map (rpair Ss) (Graph.all_succs C [c]);

in

fun add_arities pp classes (t, ars) arities =
  let val ars' =
    Symtab.lookup_list arities t
    |> fold_rev (fold_rev (insert pp classes t)) (map (complete classes) ars)
  in Symtab.update (t, ars') arities end;

fun add_arities_table pp classes = Symtab.fold (fn (t, ars) =>
  add_arities pp classes (t, map (apsnd (map (norm_sort classes))) ars));

fun rebuild_arities pp classes arities =
  Symtab.empty
  |> add_arities_table pp classes arities;

fun merge_arities pp classes (arities1, arities2) =
  Symtab.empty
  |> add_arities_table pp classes arities1
  |> add_arities_table pp classes arities2;

end;

end;
