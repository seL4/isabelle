(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Axiomatic type classes: managing predicates and parameter collections.
*)

signature AX_CLASS =
sig
  val print_axclasses: theory -> unit
  val get_info: theory -> class -> {def: thm, intro: thm, axioms: thm list}
  val get_instances: theory ->
   {classes: unit Graph.T,
    classrel: ((class * class) * thm) list,
    arities: ((string * sort list * class) * thm) list}
  val class_intros: theory -> thm list
  val params_of: theory -> class -> string list
  val all_params_of: theory -> sort -> string list
  val cert_classrel: theory -> class * class -> class * class
  val read_classrel: theory -> xstring * xstring -> class * class
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
  val prove_classrel: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
  val add_axclass: bstring * xstring list -> string list ->
    ((bstring * Attrib.src list) * string list) list -> theory -> class * theory
  val add_axclass_i: bstring * class list -> string list ->
    ((bstring * attribute list) * term list) list -> theory -> class * theory
end;

structure AxClass: AX_CLASS =
struct


(** theory data **)

(* class parameters (canonical order) *)

type param = string * class;

fun add_param pp ((x, c): param) params =
  (case AList.lookup (op =) params x of
    NONE => (x, c) :: params
  | SOME c' => error ("Duplicate class parameter " ^ quote x ^
      " for " ^ Pretty.string_of_sort pp [c] ^
      (if c = c' then "" else " and " ^ Pretty.string_of_sort pp [c'])));

fun merge_params _ ([], qs) = qs
  | merge_params pp (ps, qs) =
      fold_rev (fn q => if member (op =) ps q then I else add_param pp q) qs ps;


(* axclass *)

val introN = "intro";
val axiomsN = "axioms";

datatype axclass = AxClass of
 {def: thm,
  intro: thm,
  axioms: thm list};

type axclasses = axclass Symtab.table * param list;

fun make_axclass (def, intro, axioms) =
  AxClass {def = def, intro = intro, axioms = axioms};

fun merge_axclasses pp ((tab1, params1), (tab2, params2)) : axclasses =
  (Symtab.merge (K true) (tab1, tab2), merge_params pp (params1, params2));


(* instances *)

datatype instances = Instances of
 {classes: unit Graph.T,                 (*raw relation -- no closure!*)
  classrel: ((class * class) * thm) list,
  arities: ((string * sort list * class) * thm) list};

fun make_instances (classes, classrel, arities) =
  Instances {classes = classes, classrel = classrel, arities = arities};

fun map_instances f (Instances {classes, classrel, arities}) =
  make_instances (f (classes, classrel, arities));

fun merge_instances
   (Instances {classes = classes1, classrel = classrel1, arities = arities1},
    Instances {classes = classes2, classrel = classrel2, arities = arities2}) =
  make_instances
   (Graph.merge (K true) (classes1, classes2),
    merge (eq_fst op =) (classrel1, classrel2),
    merge (eq_fst op =) (arities1, arities2));


(* data *)

structure AxClassData = TheoryDataFun
(struct
  val name = "Pure/axclass";
  type T = axclasses * instances;
  val empty : T = ((Symtab.empty, []), make_instances (Graph.empty, [], []));
  val copy = I;
  val extend = I;
  fun merge pp ((axclasses1, instances1), (axclasses2, instances2)) =
    (merge_axclasses pp (axclasses1, axclasses2), merge_instances (instances1, instances2));
  fun print _ _ = ();
end);

val _ = Context.add_setup AxClassData.init;


(* lookup classes *)

val lookup_info = Symtab.lookup o #1 o #1 o AxClassData.get;

fun get_info thy c =
  (case lookup_info thy c of
    SOME (AxClass info) => info
  | NONE => error ("Unknown axclass " ^ quote c));

fun class_intros thy =
  let
    fun add_intro c =
      (case lookup_info thy c of SOME (AxClass {intro, ...}) => cons intro | _ => I);
    val classes = Sign.classes thy;
  in map (Thm.class_triv thy) classes @ fold add_intro classes [] end;


(* lookup parameters *)

fun get_params thy pred =
  let val params = #2 (#1 (AxClassData.get thy))
  in fold (fn (x, c) => if pred c then cons x else I) params [] end;

fun params_of thy c = get_params thy (fn c' => c' = c);
fun all_params_of thy S = get_params thy (fn c => Sign.subsort thy (S, [c]));


(* print_axclasses *)

fun print_axclasses thy =
  let
    val axclasses = #1 (#1 (AxClassData.get thy));
    val ctxt = ProofContext.init thy;

    fun pretty_axclass (class, AxClass {def, intro, axioms}) =
      Pretty.block (Pretty.fbreaks
       [Pretty.block
          [Pretty.str "axclass ", ProofContext.pretty_sort ctxt [class], Pretty.str ":"],
        Pretty.strs ("parameters:" :: params_of thy class),
        ProofContext.pretty_fact ctxt ("def", [def]),
        ProofContext.pretty_fact ctxt (introN, [intro]),
        ProofContext.pretty_fact ctxt (axiomsN, axioms)]);
  in Pretty.writeln (Pretty.chunks (map pretty_axclass (Symtab.dest axclasses))) end;



(** instances **)

val get_instances = AxClassData.get #> (fn (_, Instances insts) => insts);


(* class relations *)

fun cert_classrel thy raw_rel =
  let
    val (c1, c2) = pairself (Sign.certify_class thy) raw_rel;
    val _ = Type.add_classrel (Sign.pp thy) [(c1, c2)] (Sign.tsig_of thy);
    val _ =
      (case subtract (op =) (all_params_of thy [c1]) (all_params_of thy [c2]) of
        [] => ()
      | xs => raise TYPE ("Class " ^ Sign.string_of_sort thy [c1] ^ " lacks parameter(s) " ^
          commas_quote xs ^ " of " ^ Sign.string_of_sort thy [c2], [], []));
  in (c1, c2) end;

fun read_classrel thy raw_rel =
  cert_classrel thy (pairself (Sign.read_class thy) raw_rel)
    handle TYPE (msg, _, _) => error msg;


(* primitive rules *)

fun add_classrel th thy =
  let
    fun err () = raise THM ("add_classrel: malformed class relation", 0, [th]);
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val rel = Logic.dest_classrel prop handle TERM _ => err ();
    val (c1, c2) = cert_classrel thy rel handle TYPE _ => err ();
  in
    thy
    |> Theory.add_classrel_i [(c1, c2)]
    |> AxClassData.map (apsnd (map_instances (fn (classes, classrel, arities) =>
        (classes
            |> Graph.default_node (c1, ())
            |> Graph.default_node (c2, ())
            |> Graph.add_edge (c1, c2),
          ((c1, c2), th) :: classrel, arities))))
  end;

fun add_arity th thy =
  let
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val (t, Ss, c) = Logic.dest_arity prop handle TERM _ =>
      raise THM ("add_arity: malformed type arity", 0, [th]);
  in
    thy
    |> Theory.add_arities_i [(t, Ss, [c])]
    |> AxClassData.map (apsnd (map_instances (fn (classes, classrel, arities) =>
      (classes, classrel, ((t, Ss, c), th) :: arities))))
  end;


(* tactical proofs *)

fun prove_classrel raw_rel tac thy =
  let
    val (c1, c2) = cert_classrel thy raw_rel;
    val th = Goal.prove thy [] [] (Logic.mk_classrel (c1, c2)) (fn _ => tac) handle ERROR msg =>
      cat_error msg ("The error(s) above occurred while trying to prove class relation " ^
        quote (Sign.string_of_classrel thy [c1, c2]));
  in add_classrel th thy end;

fun prove_arity raw_arity tac thy =
  let
    val arity = Sign.cert_arity thy raw_arity;
    val props = Logic.mk_arities arity;
    val ths = Goal.prove_multi thy [] [] props
      (fn _ => Tactic.precise_conjunction_tac (length props) 1 THEN tac) handle ERROR msg =>
        cat_error msg ("The error(s) above occurred while trying to prove type arity " ^
          quote (Sign.string_of_arity thy arity));
  in fold add_arity ths thy end;



(** axclass definitions **)

(* add_axclass(_i) *)

fun gen_axclass prep_class prep_att prep_propp
    (bclass, raw_super) params raw_specs thy =
  let
    val ctxt = ProofContext.init thy;
    val pp = ProofContext.pp ctxt;


    (* prepare specification *)

    val bconst = Logic.const_of_class bclass;
    val class = Sign.full_name thy bclass;
    val super = map (prep_class thy) raw_super |> Sign.certify_sort thy;

    fun prep_axiom t =
      (case Term.add_tfrees t [] of
        [(a, S)] =>
          if Sign.subsort thy (super, S) then t
          else error ("Sort constraint of type variable " ^
            setmp show_sorts true (Pretty.string_of_typ pp) (TFree (a, S)) ^
            " needs to be weaker than " ^ Pretty.string_of_sort pp super)
      | [] => t
      | _ => error ("Multiple type variables in class axiom:\n" ^ Pretty.string_of_term pp t))
      |> map_term_types (Term.map_atyps (fn TFree _ => Term.aT [] | U => U))
      |> Logic.close_form;

    val axiomss = prep_propp (ctxt, map (map (rpair ([], [])) o snd) raw_specs)
      |> snd |> map (map (prep_axiom o fst));
    val name_atts = Attrib.map_specs (prep_att thy) raw_specs |> map fst;


    (* definition *)

    val conjs = map (curry Logic.mk_inclass (Term.aT [])) super @ List.concat axiomss;
    val class_eq =
      Logic.mk_equals (Logic.mk_inclass (Term.aT [], class), Logic.mk_conjunction_list conjs);

    val ([def], def_thy) =
      thy
      |> Theory.add_classes_i [(bclass, super)]
      |> PureThy.add_defs_i false [((Thm.def_name bconst, class_eq), [])];
    val (raw_intro, (raw_classrel, raw_axioms)) =
      (Conjunction.split_defined (length conjs) def) ||> chop (length super);


    (* facts *)

    val class_triv = Thm.class_triv def_thy class;
    val ([(_, [intro]), (_, axioms)], facts_thy) =
      def_thy
      |> PureThy.note_thmss_qualified "" bconst
        [((introN, []), [([Drule.standard raw_intro], [])]),
         ((axiomsN, []), [(map (fn th => Drule.standard (class_triv RS th)) raw_axioms, [])])]
      ||> fold (fn th => add_classrel (Drule.standard' (class_triv RS th))) raw_classrel;


    (* result *)

    val result_thy =
      facts_thy
      |> Sign.add_path bconst
      |> PureThy.note_thmss_i "" (name_atts ~~ map Thm.simple_fact (unflat axiomss axioms)) |> snd
      |> Sign.restore_naming facts_thy
      |> AxClassData.map (apfst (fn (is, ps) =>
        (Symtab.update (class, make_axclass (def, intro, axioms)) is,
          fold (fn x => add_param pp (x, class)) params ps)));

  in (class, result_thy) end;

val add_axclass = gen_axclass Sign.read_class Attrib.attribute ProofContext.read_propp;
val add_axclass_i = gen_axclass Sign.certify_class (K I) ProofContext.cert_propp;

end;
