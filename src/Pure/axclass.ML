(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Axiomatic type classes: managing predicates and parameter collections.
*)

signature AX_CLASS =
sig
  val print_axclasses: theory -> unit
  val get_info: theory -> class -> {def: thm, intro: thm, axioms: thm list}
  val class_intros: theory -> thm list
  val params_of: theory -> class -> string list
  val all_params_of: theory -> sort -> string list
  val cert_classrel: theory -> class * class -> class * class
  val read_classrel: theory -> xstring * xstring -> class * class
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
  val prove_classrel: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
  val of_sort: theory -> typ * sort -> thm list
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
  arities: ((class * sort list) * thm) list Symtab.table,
  types: (class * thm) list Typtab.table};

fun make_instances (classes, classrel, arities, types) =
  Instances {classes = classes, classrel = classrel, arities = arities, types = types};

fun map_instances f (Instances {classes, classrel, arities, types}) =
  make_instances (f (classes, classrel, arities, types));

fun merge_instances
   (Instances {classes = classes1, classrel = classrel1, arities = arities1, types = types1},
    Instances {classes = classes2, classrel = classrel2, arities = arities2, types = types2}) =
  make_instances
   (Graph.merge (K true) (classes1, classes2),
    merge (eq_fst op =) (classrel1, classrel2),
    Symtab.join (K (merge (eq_fst op =))) (arities1, arities2),
    Typtab.join (K (merge (eq_fst op =))) (types1, types2));


(* data *)

structure AxClassData = TheoryDataFun
(struct
  val name = "Pure/axclass";
  type T = axclasses * instances ref;
  val empty : T =
    ((Symtab.empty, []), ref (make_instances (Graph.empty, [], Symtab.empty, Typtab.empty)));
  fun copy (axclasses, ref instances) : T = (axclasses, ref instances);
  val extend = copy;
  fun merge pp ((axclasses1, ref instances1), (axclasses2, ref instances2)) =
    (merge_axclasses pp (axclasses1, axclasses2), ref (merge_instances (instances1, instances2)));
  fun print _ _ = ();
end);

val _ = Context.add_setup AxClassData.init;


(* classes *)

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


(* parameters *)

fun get_params thy pred =
  let val params = #2 (#1 (AxClassData.get thy))
  in fold (fn (x, c) => if pred c then cons x else I) params [] end;

fun params_of thy c = get_params thy (fn c' => c' = c);
fun all_params_of thy S = get_params thy (fn c => Sign.subsort thy (S, [c]));


(* instances *)

val get_instances = AxClassData.get #> (fn (_, ref (Instances insts)) => insts);

fun store_instance f thy (x, th) =
  let
    val th' = Drule.standard' th;
    val _ = change (#2 (AxClassData.get thy)) (map_instances (f (x, th')));
  in th' end;

val store_classrel = store_instance (fn ((c1, c2), th) => fn (classes, classrel, arities, types) =>
  (classes
    |> Graph.default_node (c1, ())
    |> Graph.default_node (c2, ())
    |> Graph.add_edge (c1, c2),
    insert (eq_fst op =) ((c1, c2), th) classrel, arities, types));

val store_arity = store_instance (fn ((t, Ss, c), th) => fn (classes, classrel, arities, types) =>
  (classes, classrel, arities |> Symtab.insert_list (eq_fst op =) (t, ((c, Ss), th)), types));

val store_type = store_instance (fn ((T, c), th) => fn (classes, classrel, arities, types) =>
  (classes, classrel, arities, types |> Typtab.insert_list (eq_fst op =) (T, (c, th))));


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



(** instance proofs **)

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
    val thy' = thy |> Theory.add_classrel_i [(c1, c2)];
    val _ = store_classrel thy' ((c1, c2), Drule.unconstrainTs th);
  in thy' end;

fun add_arity th thy =
  let
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val (t, Ss, c) = Logic.dest_arity prop handle TERM _ =>
      raise THM ("add_arity: malformed type arity", 0, [th]);
    val thy' = thy |> Theory.add_arities_i [(t, Ss, [c])];
    val _ = store_arity thy' ((t, Ss, c), Drule.unconstrainTs th);
  in thy' end;


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


(* derived instances -- cached *)

fun derive_classrel thy (c1, c2) =
  let
    val {classes, classrel, ...} = get_instances thy;
    val lookup = AList.lookup (op =) classrel;
    fun derive [c, c'] = the (lookup (c, c'))
      | derive (c :: c' :: cs) = derive [c, c'] RS derive (c' :: cs);
  in
    (case lookup (c1, c2) of
      SOME rule => rule
    | NONE =>
        (case Graph.find_paths classes (c1, c2) of
          [] => error ("Cannot derive class relation " ^ Sign.string_of_classrel thy [c1, c2])
        | path :: _ => store_classrel thy ((c1, c2), derive path)))
  end;

fun weaken_subclass thy (c1, th) c2 =
  if c1 = c2 then th
  else th RS derive_classrel thy (c1, c2);

fun weaken_subsort thy S1 S2 = S2 |> map (fn c2 =>
  (case S1 |> find_first (fn (c1, _) => Sign.subsort thy ([c1], [c2])) of
    SOME c1 => weaken_subclass thy c1 c2
  | NONE => error ("Cannot derive subsort relation " ^
      Sign.string_of_sort thy (map #1 S1) ^ " < " ^ Sign.string_of_sort thy S2)));

fun apply_arity thy t dom c =
  let
    val {arities, ...} = get_instances thy;
    val subsort = Sign.subsort thy;
    val Ss = map (map #1) dom;
  in
    (case Symtab.lookup_list arities t |> find_first (fn ((c', Ss'), _) =>
        subsort ([c'], [c]) andalso ListPair.all subsort (Ss, Ss')) of
      SOME ((c', Ss'), rule) =>
        weaken_subclass thy (c', rule OF flat (map2 (weaken_subsort thy) dom Ss')) c
    | NONE => error ("Cannot derive type arity " ^ Sign.string_of_arity thy (t, Ss, [c])))
  end;

fun derive_type thy hyps =
  let
    fun derive (Type (a, Ts)) S =
          let val Ss = Sign.arity_sorts thy a S
          in map (apply_arity thy a (map2 (fn T => fn S => S ~~ derive T S) Ts Ss)) S end
      | derive (TFree (a, [])) S =
          weaken_subsort thy (the_default [] (AList.lookup (op =) hyps a)) S
      | derive T _ = error ("Illegal occurrence of type variable " ^
          setmp show_sorts true (Sign.string_of_typ thy) T);
  in derive end;

fun of_sort thy (typ, sort) =
  let
    fun lookup () = AList.lookup (op =) (Typtab.lookup_list (#types (get_instances thy)) typ);
    val sort' = filter (is_none o lookup ()) sort;
    val _ = conditional (not (null sort')) (fn () =>
      let
        val vars = Term.fold_atyps (insert (op =)) typ [];
        val renaming =
          map2 (fn T => fn a => (T, (a, case T of TFree (_, S) => S | TVar (_, S) => S)))
            vars (Term.invent_names [] "'a" (length vars));
        val typ' = typ |> Term.map_atyps
          (fn T => TFree (#1 (the (AList.lookup (op =) renaming T)), []));

        val hyps = renaming |> map (fn (_, (a, S)) => (a, S ~~ (S |> map (fn c =>
          Thm.assume (Thm.cterm_of thy (Logic.mk_inclass (TFree (a, []), c)))))));
        val inst = renaming |> map (fn (T, (a, S)) =>
          pairself (Thm.ctyp_of thy) (TVar ((a, 0), S), T));

        val ths =
          derive_type thy hyps typ' sort'
          |> map (Thm.instantiate (inst, []));
        val _ = map (store_type thy) (map (pair typ) sort' ~~ ths);
      in () end);
  in map (the o lookup ()) sort end;



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

    val conjs = map (curry Logic.mk_inclass (Term.aT [])) super @ flat axiomss;
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
         ((axiomsN, []), [(map (fn th => Drule.standard (class_triv RS th)) raw_axioms, [])])];
    val _ = map (store_classrel facts_thy)
      (map (pair class) super ~~ map Drule.standard raw_classrel);


    (* result *)

    val result_thy =
      facts_thy
      |> Sign.add_path bconst
      |> PureThy.note_thmss_i "" (name_atts ~~ map Thm.simple_fact (unflat axiomss axioms)) |> snd
      |> Sign.restore_naming facts_thy
      |> AxClassData.map (apfst (fn (axclasses, parameters) =>
        (Symtab.update (class, make_axclass (def, intro, axioms)) axclasses,
          fold (fn x => add_param pp (x, class)) params parameters)));

  in (class, result_thy) end;

val add_axclass = gen_axclass Sign.read_class Attrib.attribute ProofContext.read_propp;
val add_axclass_i = gen_axclass Sign.certify_class (K I) ProofContext.cert_propp;

end;
