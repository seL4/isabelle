(*  Title:      Pure/sorts.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

The order-sorted algebra of type classes.

Classes denote (possibly empty) collections of types that are
partially ordered by class inclusion. They are represented
symbolically by strings.

Sorts are intersections of finitely many classes. They are represented
by lists of classes.  Normal forms of sorts are sorted lists of
minimal classes (wrt. current class inclusion).
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
  type algebra
  val rep_algebra: algebra ->
   {classes: stamp Graph.T,
    arities: (class * (class * sort list)) list Symtab.table}
  val classes: algebra -> class list
  val super_classes: algebra -> class -> class list
  val class_less: algebra -> class * class -> bool
  val class_le: algebra -> class * class -> bool
  val sort_eq: algebra -> sort * sort -> bool
  val sort_le: algebra -> sort * sort -> bool
  val sorts_le: algebra -> sort list * sort list -> bool
  val inter_sort: algebra -> sort * sort -> sort
  val certify_class: algebra -> class -> class    (*exception TYPE*)
  val certify_sort: algebra -> sort -> sort       (*exception TYPE*)
  val add_class: Pretty.pp -> class * class list -> algebra -> algebra
  val add_classrel: Pretty.pp -> class * class -> algebra -> algebra
  val add_arities: Pretty.pp -> string * (class * sort list) list -> algebra -> algebra
  val empty_algebra: algebra
  val merge_algebra: Pretty.pp -> algebra * algebra -> algebra
  type class_error
  val class_error: Pretty.pp -> class_error -> 'a
  exception CLASS_ERROR of class_error
  val mg_domain: algebra -> string -> sort -> sort list   (*exception CLASS_ERROR*)
  val of_sort: algebra -> typ * sort -> bool
  val of_sort_derivation: Pretty.pp -> algebra ->
    {classrel: 'a * class -> class -> 'a,
     constructor: string -> ('a * class) list list -> class -> 'a,
     variable: typ -> ('a * class) list} ->
    typ * sort -> 'a list   (*exception CLASS_ERROR*)
  val witness_sorts: algebra -> string list -> sort list -> sort list -> (typ * sort) list
end;

structure Sorts: SORTS =
struct


(** ordered lists of sorts **)

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



(** order-sorted algebra **)

(*
  classes: graph representing class declarations together with proper
    subclass relation, which needs to be transitive and acyclic.

  arities: table of association lists of all type arities; (t, ars)
    means that type constructor t has the arities ars; an element
    (c, (c0, Ss)) of ars represents the arity t::(Ss)c being derived
    via c0 <= c.  "Coregularity" of the arities structure requires
    that for any two declarations t::(Ss1)c1 and t::(Ss2)c2 such that
    c1 <= c2 holds Ss1 <= Ss2.
*)

datatype algebra = Algebra of
 {classes: stamp Graph.T,
  arities: (class * (class * sort list)) list Symtab.table};

fun rep_algebra (Algebra args) = args;

val classes_of = #classes o rep_algebra;
val arities_of = #arities o rep_algebra;

fun make_algebra (classes, arities) =
  Algebra {classes = classes, arities = arities};

fun map_classes f (Algebra {classes, arities}) = make_algebra (f classes, arities);
fun map_arities f (Algebra {classes, arities}) = make_algebra (classes, f arities);


(* classes *)

val classes = Graph.keys o classes_of;
val super_classes = Graph.imm_succs o classes_of;


(* class relations *)

val class_less = Graph.is_edge o classes_of;
fun class_le algebra (c1, c2) = c1 = c2 orelse class_less algebra (c1, c2);


(* sort relations *)

fun sort_le algebra (S1, S2) =
  forall (fn c2 => exists (fn c1 => class_le algebra (c1, c2)) S1) S2;

fun sorts_le algebra (Ss1, Ss2) =
  ListPair.all (sort_le algebra) (Ss1, Ss2);

fun sort_eq algebra (S1, S2) =
  sort_le algebra (S1, S2) andalso sort_le algebra (S2, S1);


(* intersection *)

fun inter_class algebra c S =
  let
    fun intr [] = [c]
      | intr (S' as c' :: c's) =
          if class_le algebra (c', c) then S'
          else if class_le algebra (c, c') then intr c's
          else c' :: intr c's
  in intr S end;

fun inter_sort algebra (S1, S2) =
  sort_strings (fold (inter_class algebra) S1 S2);


(* normal form *)

fun norm_sort _ [] = []
  | norm_sort _ (S as [_]) = S
  | norm_sort algebra S =
      filter (fn c => not (exists (fn c' => class_less algebra (c', c)) S)) S
      |> sort_distinct string_ord;


(* certify *)

fun certify_class algebra c =
  if can (Graph.get_node (classes_of algebra)) c then c
  else raise TYPE ("Undeclared class: " ^ quote c, [], []);

fun certify_sort classes = norm_sort classes o map (certify_class classes);



(** build algebras **)

(* classes *)

fun err_dup_classes cs =
  error ("Duplicate declaration of class(es): " ^ commas_quote cs);

fun err_cyclic_classes pp css =
  error (cat_lines (map (fn cs =>
    "Cycle in class relation: " ^ Pretty.string_of_classrel pp cs) css));

fun add_class pp (c, cs) = map_classes (fn classes =>
  let
    val classes' = classes |> Graph.new_node (c, stamp ())
      handle Graph.DUP dup => err_dup_classes [dup];
    val classes'' = classes' |> fold Graph.add_edge_trans_acyclic (map (pair c) cs)
      handle Graph.CYCLES css => err_cyclic_classes pp css;
  in classes'' end);


(* arities *)

local

fun for_classes _ NONE = ""
  | for_classes pp (SOME (c1, c2)) =
      " for classes " ^ Pretty.string_of_classrel pp [c1, c2];

fun err_conflict pp t cc (c, Ss) (c', Ss') =
  error ("Conflict of type arities" ^ for_classes pp cc ^ ":\n  " ^
    Pretty.string_of_arity pp (t, Ss, [c]) ^ " and\n  " ^
    Pretty.string_of_arity pp (t, Ss', [c']));

fun coregular pp algebra t (c, (c0, Ss)) ars =
  let
    fun conflict (c', (_, Ss')) =
      if class_le algebra (c, c') andalso not (sorts_le algebra (Ss, Ss')) then
        SOME ((c, c'), (c', Ss'))
      else if class_le algebra (c', c) andalso not (sorts_le algebra (Ss', Ss)) then
        SOME ((c', c), (c', Ss'))
      else NONE;
  in
    (case get_first conflict ars of
      SOME ((c1, c2), (c', Ss')) => err_conflict pp t (SOME (c1, c2)) (c, Ss) (c', Ss')
    | NONE => (c, (c0, Ss)) :: ars)
  end;

fun complete algebra (c0, Ss) = map (rpair (c0, Ss)) (c0 :: super_classes algebra c0);

fun insert pp algebra t (c, (c0, Ss)) ars =
  (case AList.lookup (op =) ars c of
    NONE => coregular pp algebra t (c, (c0, Ss)) ars
  | SOME (_, Ss') =>
      if sorts_le algebra (Ss, Ss') then ars
      else if sorts_le algebra (Ss', Ss) then
        coregular pp algebra t (c, (c0, Ss))
          (filter_out (fn (c'', (_, Ss'')) => c = c'' andalso Ss'' = Ss') ars)
      else err_conflict pp t NONE (c, Ss) (c, Ss'));

fun insert_ars pp algebra (t, ars) arities =
  let val ars' =
    Symtab.lookup_list arities t
    |> fold_rev (fold_rev (insert pp algebra t)) (map (complete algebra) ars)
  in Symtab.update (t, ars') arities end;

in

fun add_arities pp arg algebra = algebra |> map_arities (insert_ars pp algebra arg);

fun add_arities_table pp algebra =
  Symtab.fold (fn (t, ars) => insert_ars pp algebra (t, map snd ars));

end;


(* classrel *)

fun rebuild_arities pp algebra = algebra |> map_arities (fn arities =>
  Symtab.empty
  |> add_arities_table pp algebra arities);

fun add_classrel pp rel = rebuild_arities pp o map_classes (fn classes =>
  classes |> Graph.add_edge_trans_acyclic rel
    handle Graph.CYCLES css => err_cyclic_classes pp css);


(* empty and merge *)

val empty_algebra = make_algebra (Graph.empty, Symtab.empty);

fun merge_algebra pp
   (Algebra {classes = classes1, arities = arities1},
    Algebra {classes = classes2, arities = arities2}) =
  let
    val classes' = Graph.merge_trans_acyclic (op =) (classes1, classes2)
      handle Graph.DUPS cs => err_dup_classes cs
          | Graph.CYCLES css => err_cyclic_classes pp css;
    val algebra0 = make_algebra (classes', Symtab.empty);
    val arities' = Symtab.empty
      |> add_arities_table pp algebra0 arities1
      |> add_arities_table pp algebra0 arities2;
  in make_algebra (classes', arities') end;



(** sorts of types **)

(* errors *)

datatype class_error = NoClassrel of class * class | NoArity of string * class;

fun class_error pp (NoClassrel (c1, c2)) =
      error ("No class relation " ^ Pretty.string_of_classrel pp [c1, c2])
  | class_error pp (NoArity (a, c)) =
      error ("No type arity " ^ Pretty.string_of_arity pp (a, [], [c]));

exception CLASS_ERROR of class_error;


(* mg_domain *)

fun mg_domain algebra a S =
  let
    val arities = arities_of algebra;
    fun dom c =
      (case AList.lookup (op =) (Symtab.lookup_list arities a) c of
        NONE => raise CLASS_ERROR (NoArity (a, c))
      | SOME (_, Ss) => Ss);
    fun dom_inter c Ss = ListPair.map (inter_sort algebra) (dom c, Ss);
  in
    (case S of
      [] => raise Fail "Unknown domain of empty intersection"
    | c :: cs => fold dom_inter cs (dom c))
  end;


(* of_sort *)

fun of_sort algebra =
  let
    fun ofS (_, []) = true
      | ofS (TFree (_, S), S') = sort_le algebra (S, S')
      | ofS (TVar (_, S), S') = sort_le algebra (S, S')
      | ofS (Type (a, Ts), S) =
          let val Ss = mg_domain algebra a S in
            ListPair.all ofS (Ts, Ss)
          end handle CLASS_ERROR _ => false;
  in ofS end;


(* of_sort_derivation *)

fun of_sort_derivation pp algebra {classrel, constructor, variable} =
  let
    val {classes, arities} = rep_algebra algebra;
    fun weaken_path (x, c1 :: c2 :: cs) = weaken_path (classrel (x, c1) c2, c2 :: cs)
      | weaken_path (x, _) = x;
    fun weaken (x, c1) c2 =
      (case Graph.irreducible_paths classes (c1, c2) of
        [] => raise CLASS_ERROR (NoClassrel (c1, c2))
      | cs :: _ => weaken_path (x, cs));

    fun weakens S1 S2 = S2 |> map (fn c2 =>
      (case S1 |> find_first (fn (_, c1) => class_le algebra (c1, c2)) of
        SOME d1 => weaken d1 c2
      | NONE => error ("Cannot derive subsort relation " ^
          Pretty.string_of_sort pp (map #2 S1) ^ " < " ^ Pretty.string_of_sort pp S2)));

    fun derive _ [] = []
      | derive (Type (a, Ts)) S =
          let
            val Ss = mg_domain algebra a S;
            val dom = map2 (fn T => fn S => derive T S ~~ S) Ts Ss;
          in
            S |> map (fn c =>
              let
                val (c0, Ss') = the (AList.lookup (op =) (Symtab.lookup_list arities a) c);
                val dom' = map2 (fn d => fn S' => weakens d S' ~~ S') dom Ss';
              in weaken (constructor a dom' c0, c0) c end)
          end
      | derive T S = weakens (variable T) S;
  in uncurry derive end;


(* witness_sorts *)

fun witness_sorts algebra types hyps sorts =
  let
    fun le S1 S2 = sort_le algebra (S1, S2);
    fun get_solved S2 (T, S1) = if le S1 S2 then SOME (T, S2) else NONE;
    fun get_hyp S2 S1 = if le S1 S2 then SOME (TFree ("'hyp", S1), S2) else NONE;
    fun mg_dom t S = SOME (mg_domain algebra t S) handle CLASS_ERROR _ => NONE;

    fun witn_sort _ [] solved_failed = (SOME (propT, []), solved_failed)
      | witn_sort path S (solved, failed) =
          if exists (le S) failed then (NONE, (solved, failed))
          else
            (case get_first (get_solved S) solved of
              SOME w => (SOME w, (solved, failed))
            | NONE =>
                (case get_first (get_hyp S) hyps of
                  SOME w => (SOME w, (w :: solved, failed))
                | NONE => witn_types path types S (solved, failed)))

    and witn_sorts path x = fold_map (witn_sort path) x

    and witn_types _ [] S (solved, failed) = (NONE, (solved, S :: failed))
      | witn_types path (t :: ts) S solved_failed =
          (case mg_dom t S of
            SOME SS =>
              (*do not descend into stronger args (achieving termination)*)
              if exists (fn D => le D S orelse exists (le D) path) SS then
                witn_types path ts S solved_failed
              else
                let val (ws, (solved', failed')) = witn_sorts (S :: path) SS solved_failed in
                  if forall is_some ws then
                    let val w = (Type (t, map (#1 o the) ws), S)
                    in (SOME w, (w :: solved', failed')) end
                  else witn_types path ts S (solved', failed')
                end
          | NONE => witn_types path ts S solved_failed);

  in map_filter I (#1 (witn_sorts [] sorts ([], []))) end;

end;
