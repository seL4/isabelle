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
  type cache
  val cache: cache
  val of_sort: theory -> typ * sort -> cache -> thm list * cache  (*exception Sorts.CLASS_ERROR*)
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

type instances =
  ((class * class) * thm) list *
  ((class * sort list) * thm) list Symtab.table;

fun merge_instances ((classrel1, arities1): instances, (classrel2, arities2)) =
 (merge (eq_fst op =) (classrel1, classrel2),
  Symtab.join (K (merge (eq_fst op =))) (arities1, arities2));


(* setup data *)

structure AxClassData = TheoryDataFun
(struct
  val name = "Pure/axclass";
  type T = axclasses * instances;
  val empty : T = ((Symtab.empty, []), ([], Symtab.empty));
  val copy = I;
  val extend = I;
  fun merge pp ((axclasses1, instances1), (axclasses2, instances2)) =
    (merge_axclasses pp (axclasses1, axclasses2), (merge_instances (instances1, instances2)));
  fun print _ _ = ();
end);

val _ = Context.add_setup AxClassData.init;


(* maintain axclasses *)

val get_axclasses = #1 o AxClassData.get;
fun map_axclasses f = AxClassData.map (apfst f);

val lookup_def = Symtab.lookup o #1 o get_axclasses;

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


fun get_params thy pred =
  let val params = #2 (get_axclasses thy);
  in fold (fn (x, c) => if pred c then cons x else I) params [] end;

fun params_of thy c = get_params thy (fn c' => c' = c);
fun all_params_of thy S = get_params thy (fn c => Sign.subsort thy (S, [c]));


(* maintain instances *)

val get_instances = #2 o AxClassData.get;
fun map_instances f = AxClassData.map (apsnd f);


fun the_classrel thy (c1, c2) =
  (case AList.lookup (op =) (#1 (get_instances thy)) (c1, c2) of
    SOME th => Thm.transfer thy th
  | NONE => error ("Unproven class relation " ^ Sign.string_of_classrel thy [c1, c2]));

fun put_classrel arg = map_instances (fn (classrel, arities) =>
  (insert (eq_fst op =) arg classrel, arities));


fun the_arity thy a (c, Ss) =
  (case AList.lookup (op =) (Symtab.lookup_list (#2 (get_instances thy)) a) (c, Ss)  of
    SOME th => Thm.transfer thy th
  | NONE => error ("Unproven type arity " ^ Sign.string_of_arity thy (a, Ss, [c])));

fun put_arity ((t, Ss, c), th) = map_instances (fn (classrel, arities) =>
  (classrel, arities |> Symtab.insert_list (eq_fst op =) (t, ((c, Ss), th))));


(* print data *)

fun print_axclasses thy =
  let
    val axclasses = #1 (get_axclasses thy);
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
  in
    thy
    |> Sign.primitive_classrel (c1, c2)
    |> put_classrel ((c1, c2), Drule.unconstrainTs th)
  end;

fun add_arity th thy =
  let
    fun err () = raise THM ("add_arity: malformed type arity", 0, [th]);
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val (t, Ss, c) = Logic.dest_arity prop handle TERM _ => err ();
    val _ = if map (Sign.certify_sort thy) Ss = Ss then () else err ();
  in
    thy
    |> Sign.primitive_arity (t, Ss, [c])
    |> put_arity ((t, Ss, c), Drule.unconstrainTs th)
  end;


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


    (* result *)

    val result_thy =
      facts_thy
      |> fold put_classrel (map (pair class) super ~~ classrel)
      |> Sign.add_path bconst
      |> PureThy.note_thmss_i "" (name_atts ~~ map Thm.simple_fact (unflat axiomss axioms)) |> snd
      |> Sign.restore_naming facts_thy
      |> map_axclasses (fn (axclasses, parameters) =>
        (Symtab.update (class, make_axclass (def, intro, axioms)) axclasses,
          fold (fn x => add_param pp (x, class)) params parameters));

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

datatype cache = Types of (class * thm) list Typtab.table;
val cache = Types Typtab.empty;

local

fun lookup_type (Types cache) = AList.lookup (op =) o Typtab.lookup_list cache;
fun insert_type T der (Types cache) = Types (Typtab.insert_list (eq_fst op =) (T, der) cache);

fun derive_type _ (_, []) = []
  | derive_type thy (typ, sort) =
      let
        val vars = Term.fold_atyps
            (fn T as TFree (_, S) => insert (eq_fst op =) (T, S)
              | T as TVar (_, S) => insert (eq_fst op =) (T, S)
              | _ => I) typ [];
        val hyps = vars
          |> map (fn (T, S) => (T, Drule.sort_triv thy (T, S) ~~ S));
        val ths = (typ, sort)
          |> Sorts.of_sort_derivation (Sign.pp thy) (Sign.classes_of thy, Sign.arities_of thy)
           {classrel =
              fn (th, c1) => fn c2 => th RS the_classrel thy (c1, c2),
            constructor =
              fn a => fn dom => fn c =>
                let val Ss = map (map snd) dom and ths = maps (map fst) dom
                in ths MRS the_arity thy a (c, Ss) end,
            variable =
              the_default [] o AList.lookup (op =) hyps};
      in ths end;

in

fun of_sort thy (typ, sort) cache =
  let
    val sort' = filter (is_none o lookup_type cache typ) sort;
    val ths' = derive_type thy (typ, sort')
      handle ERROR msg => cat_error msg ("The error(s) above occurred for sort derivation: " ^
        Sign.string_of_typ thy typ ^ " :: " ^ Sign.string_of_sort thy sort');
    val cache' = cache |> fold (insert_type typ) (sort' ~~ ths');
    val ths =
      sort |> map (fn c =>
        Goal.finish (the (lookup_type cache' typ c) RS
          Goal.init (Thm.cterm_of thy (Logic.mk_inclass (typ, c))))
        |> Thm.adjust_maxidx_thm);
  in (ths, cache') end;

end;

end;
