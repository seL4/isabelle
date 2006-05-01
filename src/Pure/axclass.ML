(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Type classes as parameter records and predicates, with explicit
definitions and proofs.
*)

signature AX_CLASS =
sig
  val get_definition: theory -> class -> {def: thm, intro: thm, axioms: thm list}
  val class_intros: theory -> thm list
  val params_of: theory -> class -> string list
  val all_params_of: theory -> sort -> string list
  val print_axclasses: theory -> unit
  val cert_classrel: theory -> class * class -> class * class
  val read_classrel: theory -> xstring * xstring -> class * class
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
  val prove_classrel: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
  val define_class: bstring * xstring list -> string list ->
    ((bstring * Attrib.src list) * string list) list -> theory -> class * theory
  val define_class_i: bstring * class list -> string list ->
    ((bstring * attribute list) * term list) list -> theory -> class * theory
  val axiomatize_class: bstring * xstring list -> theory -> theory
  val axiomatize_class_i: bstring * class list -> theory -> theory
  val axiomatize_classrel: (xstring * xstring) list -> theory -> theory
  val axiomatize_classrel_i: (class * class) list -> theory -> theory
  val axiomatize_arity: xstring * string list * string -> theory -> theory
  val axiomatize_arity_i: arity -> theory -> theory
  val of_sort: theory -> typ * sort -> thm list
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


(* axclasses *)

val introN = "intro";
val superN = "super";
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

val classrelN = "classrel";
val arityN = "arity";

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


(* setup data *)

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


(* retrieve axclasses *)

val lookup_def = Symtab.lookup o #1 o #1 o AxClassData.get;

fun get_definition thy c =
  (case lookup_def thy c of
    SOME (AxClass info) => info
  | NONE => error ("Undefined type class " ^ quote c));

fun class_intros thy =
  let
    fun add_intro c =
      (case lookup_def thy c of SOME (AxClass {intro, ...}) => cons intro | _ => I);
    val classes = Sign.classes thy;
  in map (Thm.class_triv thy) classes @ fold add_intro classes [] end;


(* retrieve parameters *)

fun get_params thy pred =
  let val params = #2 (#1 (AxClassData.get thy))
  in fold (fn (x, c) => if pred c then cons x else I) params [] end;

fun params_of thy c = get_params thy (fn c' => c' = c);
fun all_params_of thy S = get_params thy (fn c => Sign.subsort thy (S, [c]));


(* maintain instances *)

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


(* print data *)

fun print_axclasses thy =
  let
    val axclasses = #1 (#1 (AxClassData.get thy));
    val ctxt = ProofContext.init thy;

    fun pretty_axclass (class, AxClass {def, intro, axioms}) =
      Pretty.block (Pretty.fbreaks
       [Pretty.block
          [Pretty.str "class ", ProofContext.pretty_sort ctxt [class], Pretty.str ":"],
        Pretty.strs ("parameters:" :: params_of thy class),
        ProofContext.pretty_fact ctxt ("def", [def]),
        ProofContext.pretty_fact ctxt (introN, [intro]),
        ProofContext.pretty_fact ctxt (axiomsN, axioms)]);
  in Pretty.writeln (Pretty.chunks (map pretty_axclass (Symtab.dest axclasses))) end;



(** instances **)

(* class relations *)

fun cert_classrel thy raw_rel =
  let
    val (c1, c2) = pairself (Sign.certify_class thy) raw_rel;
    val _ = Type.add_classrel (Sign.pp thy) (c1, c2) (Sign.tsig_of thy);
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
    val thy' = thy |> Sign.primitive_classrel (c1, c2);
    val _ = store_classrel thy' ((c1, c2), Drule.unconstrainTs th);
  in thy' end;

fun add_arity th thy =
  let
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val (t, Ss, c) = Logic.dest_arity prop handle TERM _ =>
      raise THM ("add_arity: malformed type arity", 0, [th]);
    val thy' = thy |> Sign.primitive_arity (t, Ss, [c]);
    val _ = store_arity thy' ((t, Ss, c), Drule.unconstrainTs th);
  in thy' end;


(* tactical proofs *)

fun prove_classrel raw_rel tac thy =
  let
    val (c1, c2) = cert_classrel thy raw_rel;
    val th = Goal.prove thy [] [] (Logic.mk_classrel (c1, c2)) (fn _ => tac) handle ERROR msg =>
      cat_error msg ("The error(s) above occurred while trying to prove class relation " ^
        quote (Sign.string_of_classrel thy [c1, c2]));
  in
    thy
    |> PureThy.add_thms [((classrelN ^ "_" ^ serial_string (), th), [])]
    |-> (fn [th'] => add_classrel th')
  end;

fun prove_arity raw_arity tac thy =
  let
    val arity = Sign.cert_arity thy raw_arity;
    val props = Logic.mk_arities arity;
    val ths = Goal.prove_multi thy [] [] props
      (fn _ => Tactic.precise_conjunction_tac (length props) 1 THEN tac) handle ERROR msg =>
        cat_error msg ("The error(s) above occurred while trying to prove type arity " ^
          quote (Sign.string_of_arity thy arity));
  in
    thy
    |> PureThy.add_thms (ths |> map (fn th => ((arityN ^ "_" ^ serial_string (), th), [])))
    |-> fold add_arity
  end;



(** class definitions **)

local

fun def_class prep_class prep_att prep_propp
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
      |> Sign.primitive_class (bclass, super)
      |> PureThy.add_defs_i false [((Thm.def_name bconst, class_eq), [])];
    val (raw_intro, (raw_classrel, raw_axioms)) =
      (Conjunction.split_defined (length conjs) def) ||> chop (length super);


    (* facts *)

    val class_triv = Thm.class_triv def_thy class;
    val ([(_, [intro]), (_, classrel), (_, axioms)], facts_thy) =
      def_thy
      |> PureThy.note_thmss_qualified "" bconst
        [((introN, []), [([Drule.standard raw_intro], [])]),
         ((superN, []), [(map Drule.standard raw_classrel, [])]),
         ((axiomsN, []), [(map (fn th => Drule.standard (class_triv RS th)) raw_axioms, [])])];
    val _ = map (store_classrel facts_thy) (map (pair class) super ~~ classrel);


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

in

val define_class = def_class Sign.read_class Attrib.attribute ProofContext.read_propp;
val define_class_i = def_class Sign.certify_class (K I) ProofContext.cert_propp;

end;


(** axiomatizations **)

local

fun axiomatize kind add prep arg thy =
  let val specs = arg |> prep thy |> map (fn prop => ((kind ^ "_" ^ serial_string (), prop), []))
  in thy |> PureThy.add_axioms_i specs |-> fold add end;

fun ax_classrel prep =
  axiomatize classrelN add_classrel (fn thy => map (prep thy #> Logic.mk_classrel));

fun ax_arity prep =
  axiomatize arityN add_arity (fn thy => prep thy #> Logic.mk_arities);

fun ax_class prep_class prep_classrel (bclass, raw_super) thy =
  let
    val class = Sign.full_name thy bclass;
    val super = map (prep_class thy) raw_super |> Sign.certify_sort thy;
  in
    thy
    |> Sign.primitive_class (bclass, super)
    |> ax_classrel prep_classrel (map (fn c => (class, c)) super)
  end;

in

val axiomatize_class = ax_class Sign.read_class read_classrel;
val axiomatize_class_i = ax_class Sign.certify_class cert_classrel;
val axiomatize_classrel = ax_classrel read_classrel;
val axiomatize_classrel_i = ax_classrel cert_classrel;
val axiomatize_arity = ax_arity Sign.read_arity;
val axiomatize_arity_i = ax_arity Sign.cert_arity;

end;



(** explicit derivations -- cached **)

local

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

fun derive_type _ (_, []) = []
  | derive_type thy (typ, sort) =
      let
        val hyps = Term.fold_atyps
            (fn T as TFree (_, S) => insert (eq_fst op =) (T, S)
              | T as TVar (_, S) => insert (eq_fst op =) (T, S)
              | _ => I) typ []
          |> map (fn (T, S) => (T, S ~~ Drule.sort_triv thy (T, S)));

        fun derive (Type (a, Ts)) S =
              let
                val Ss = Sign.arity_sorts thy a S;
                val ds = map (fn (T, S) => S ~~ derive T S) (Ts ~~ Ss);
              in map (apply_arity thy a ds) S end
          | derive T S = weaken_subsort thy (the_default [] (AList.lookup (op =) hyps T)) S;

        val ths = derive typ sort;
      in map (store_type thy) (map (pair typ) sort ~~ ths) end;

in

fun of_sort thy (typ, sort) =
  let
    fun lookup () = AList.lookup (op =) (Typtab.lookup_list (#types (get_instances thy)) typ);
    val _ = derive_type thy (typ, filter (is_none o lookup ()) sort);
  in map (the o lookup ()) sort end;

end;

end;
