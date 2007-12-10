(*  Title:      Pure/Isar/class.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS =
sig
  (*classes*)
  val class: bstring -> class list -> Element.context_i Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_cmd: bstring -> xstring list -> Element.context Locale.element list
    -> xstring list -> theory -> string * Proof.context

  val init: class -> theory -> Proof.context
  val logical_const: string -> Markup.property list
    -> (string * mixfix) * term -> theory -> theory
  val syntactic_const: string -> Syntax.mode -> Markup.property list
    -> (string * mixfix) * term -> theory -> theory
  val refresh_syntax: class -> Proof.context -> Proof.context

  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic
  val prove_subclass: class * class -> thm list -> Proof.context
    -> theory -> theory

  val class_prefix: string -> string
  val is_class: theory -> class -> bool
  val these_params: theory -> sort -> (string * (string * typ)) list
  val print_classes: theory -> unit

  (*instances*)
  val init_instantiation: string list * sort list * sort -> theory -> local_theory
  val prep_spec: local_theory -> term -> term
  val instantiation_instance: (local_theory -> local_theory) -> local_theory -> Proof.state
  val prove_instantiation_instance: (Proof.context -> tactic) -> local_theory -> local_theory
  val conclude_instantiation: local_theory -> local_theory
  val instantiation_param: Proof.context -> string -> string option
  val confirm_declaration: string -> local_theory -> local_theory

  (*old axclass layer*)
  val axclass_cmd: bstring * xstring list
    -> ((bstring * Attrib.src list) * string list) list
    -> theory -> class * theory
  val classrel_cmd: xstring * xstring -> theory -> Proof.state

  (*old instance layer*)
  val instance_arity: (theory -> theory) -> arity -> theory -> Proof.state
  val instance_arity_cmd: bstring * xstring list * xstring -> theory -> Proof.state
end;

structure Class : CLASS =
struct

(** auxiliary **)

val classN = "class";
val introN = "intro";

fun prove_interpretation tac prfx_atts expr inst =
  Locale.interpretation_i I prfx_atts expr inst
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun prove_interpretation_in tac after_qed (name, expr) =
  Locale.interpretation_in_locale
      (ProofContext.theory after_qed) (name, expr)
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun OF_LAST thm1 thm2 = thm1 RSN (Thm.nprems_of thm2, thm2);

fun strip_all_ofclass thy sort =
  let
    val typ = TVar ((Name.aT, 0), sort);
    fun prem_inclass t =
      case Logic.strip_imp_prems t
       of ofcls :: _ => try Logic.dest_inclass ofcls
        | [] => NONE;
    fun strip_ofclass class thm =
      thm OF (fst o AxClass.of_sort thy (typ, [class])) AxClass.cache;
    fun strip thm = case (prem_inclass o Thm.prop_of) thm
     of SOME (_, class) => thm |> strip_ofclass class |> strip
      | NONE => thm;
  in strip end;

fun get_remove_global_constraint c thy =
  let
    val ty = Sign.the_const_constraint thy c;
  in
    thy
    |> Sign.add_const_constraint (c, NONE)
    |> pair (c, Logic.unvarifyT ty)
  end;


(** primitive axclass and instance commands **)

fun axclass_cmd (class, raw_superclasses) raw_specs thy =
  let
    val ctxt = ProofContext.init thy;
    val superclasses = map (Sign.read_class thy) raw_superclasses;
    val name_atts = map ((apsnd o map) (Attrib.attribute thy) o fst)
      raw_specs;
    val axiomss = ProofContext.read_propp (ctxt, map (map (rpair []) o snd)
          raw_specs)
      |> snd
      |> (map o map) fst;
  in
    AxClass.define_class (class, superclasses) []
      (name_atts ~~ axiomss) thy
  end;

local

fun gen_instance mk_prop add_thm after_qed insts thy =
  let
    fun after_qed' results =
      ProofContext.theory ((fold o fold) add_thm results #> after_qed);
  in
    thy
    |> ProofContext.init
    |> Proof.theorem_i NONE after_qed' ((map (fn t => [(t, [])])
        o mk_prop thy) insts)
  end;

in

val instance_arity =
  gen_instance (Logic.mk_arities oo Sign.cert_arity) AxClass.add_arity;
val instance_arity_cmd =
  gen_instance (Logic.mk_arities oo Sign.read_arity) AxClass.add_arity I;
val classrel =
  gen_instance (single oo (Logic.mk_classrel oo AxClass.cert_classrel)) AxClass.add_classrel I;
val classrel_cmd =
  gen_instance (single oo (Logic.mk_classrel oo AxClass.read_classrel)) AxClass.add_classrel I;

end; (*local*)


(** class data **)

datatype class_data = ClassData of {
  consts: (string * string) list
    (*locale parameter ~> constant name*),
  base_sort: sort,
  inst: term option list
    (*canonical interpretation*),
  morphism: morphism,
    (*partial morphism of canonical interpretation*)
  intro: thm,
  defs: thm list,
  operations: (string * (class * (typ * term))) list
};

fun rep_class_data (ClassData d) = d;
fun mk_class_data ((consts, base_sort, inst, morphism, intro),
    (defs, operations)) =
  ClassData { consts = consts, base_sort = base_sort, inst = inst,
    morphism = morphism, intro = intro, defs = defs,
    operations = operations };
fun map_class_data f (ClassData { consts, base_sort, inst, morphism, intro,
    defs, operations }) =
  mk_class_data (f ((consts, base_sort, inst, morphism, intro),
    (defs, operations)));
fun merge_class_data _ (ClassData { consts = consts,
    base_sort = base_sort, inst = inst, morphism = morphism, intro = intro,
    defs = defs1, operations = operations1 },
  ClassData { consts = _, base_sort = _, inst = _, morphism = _, intro = _,
    defs = defs2, operations = operations2 }) =
  mk_class_data ((consts, base_sort, inst, morphism, intro),
    (Thm.merge_thms (defs1, defs2),
      AList.merge (op =) (K true) (operations1, operations2)));

structure ClassData = TheoryDataFun
(
  type T = class_data Graph.T
  val empty = Graph.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Graph.join merge_class_data;
);


(* queries *)

val lookup_class_data = Option.map rep_class_data oo try o Graph.get_node o ClassData.get;

fun the_class_data thy class = case lookup_class_data thy class
 of NONE => error ("Undeclared class " ^ quote class)
  | SOME data => data;

val is_class = is_some oo lookup_class_data;

val ancestry = Graph.all_succs o ClassData.get;

fun these_params thy =
  let
    fun params class =
      let
        val const_typs = (#params o AxClass.get_info thy) class;
        val const_names = (#consts o the_class_data thy) class;
      in
        (map o apsnd) (fn c => (c, (the o AList.lookup (op =) const_typs) c)) const_names
      end;
  in maps params o ancestry thy end;

fun these_defs thy = maps (these o Option.map #defs o lookup_class_data thy) o ancestry thy;

fun morphism thy = #morphism o the_class_data thy;

fun these_intros thy =
  Graph.fold (fn (_, (data, _)) => insert Thm.eq_thm ((#intro o rep_class_data) data))
    (ClassData.get thy) [];

fun these_operations thy =
  maps (#operations o the_class_data thy) o ancestry thy;

fun print_classes thy =
  let
    val ctxt = ProofContext.init thy;
    val algebra = Sign.classes_of thy;
    val arities =
      Symtab.empty
      |> Symtab.fold (fn (tyco, arities) => fold (fn (class, _) =>
           Symtab.map_default (class, []) (insert (op =) tyco)) arities)
             ((#arities o Sorts.rep_algebra) algebra);
    val the_arities = these o Symtab.lookup arities;
    fun mk_arity class tyco =
      let
        val Ss = Sorts.mg_domain algebra tyco [class];
      in Syntax.pretty_arity ctxt (tyco, Ss, [class]) end;
    fun mk_param (c, ty) = Pretty.str (Sign.extern_const thy c ^ " :: "
      ^ setmp show_sorts false (Syntax.string_of_typ ctxt o Type.strip_sorts) ty);
    fun mk_entry class = (Pretty.block o Pretty.fbreaks o map_filter I) [
      (SOME o Pretty.str) ("class " ^ Sign.extern_class thy class ^ ":"),
      (SOME o Pretty.block) [Pretty.str "supersort: ",
        (Syntax.pretty_sort ctxt o Sign.minimize_sort thy o Sign.super_classes thy) class],
      if is_class thy class then (SOME o Pretty.str)
        ("locale: " ^ Locale.extern thy class) else NONE,
      ((fn [] => NONE | ps => (SOME o Pretty.block o Pretty.fbreaks)
          (Pretty.str "parameters:" :: ps)) o map mk_param
        o these o Option.map #params o try (AxClass.get_info thy)) class,
      (SOME o Pretty.block o Pretty.breaks) [
        Pretty.str "instances:",
        Pretty.list "" "" (map (mk_arity class) (the_arities class))
      ]
    ]
  in
    (Pretty.writeln o Pretty.chunks o separate (Pretty.str "")
      o map mk_entry o Sorts.all_classes) algebra
  end;


(* updaters *)

fun add_class_data ((class, superclasses), (cs, base_sort, inst, phi, intro)) thy =
  let
    val operations = map (fn (v_ty as (_, ty), (c, _)) =>
      (c, (class, (ty, Free v_ty)))) cs;
    val cs = (map o pairself) fst cs;
    val add_class = Graph.new_node (class,
        mk_class_data ((cs, base_sort, map (SOME o Const) inst, phi, intro), ([], operations)))
      #> fold (curry Graph.add_edge class) superclasses;
  in
    ClassData.map add_class thy
  end;

fun register_operation class (c, (t, some_def)) thy =
  let
    val base_sort = (#base_sort o the_class_data thy) class;
    val prep_typ = map_atyps
      (fn TVar (vi as (v, _), sort) => if Name.aT = v
        then TFree (v, base_sort) else TVar (vi, sort));
    val t' = map_types prep_typ t;
    val ty' = Term.fastype_of t';
  in
    thy
    |> (ClassData.map o Graph.map_node class o map_class_data o apsnd)
      (fn (defs, operations) =>
        (fold cons (the_list some_def) defs,
          (c, (class, (ty', t'))) :: operations))
  end;


(** rule calculation, tactics and methods **)

val class_prefix = Logic.const_of_class o Sign.base_name;

fun calculate_morphism class cs =
  let
    val subst_typ = Term.map_type_tfree (fn var as (v, sort) =>
      if v = Name.aT then TVar ((v, 0), [class]) else TVar ((v, 0), sort));
    fun subst_aterm (t as Free (v, ty)) = (case AList.lookup (op =) cs v
         of SOME (c, _) => Const (c, ty)
          | NONE => t)
      | subst_aterm t = t;
    val subst_term = map_aterms subst_aterm #> map_types subst_typ;
  in
    Morphism.term_morphism subst_term
    $> Morphism.typ_morphism subst_typ
  end;

fun class_intro thy class sups =
  let
    fun class_elim class =
      case (#axioms o AxClass.get_info thy) class
       of [thm] => SOME (Drule.unconstrainTs thm)
        | [] => NONE;
    val pred_intro = case Locale.intros thy class
     of ([ax_intro], [intro]) => intro |> OF_LAST ax_intro |> SOME
      | ([intro], []) => SOME intro
      | ([], [intro]) => SOME intro
      | _ => NONE;
    val pred_intro' = pred_intro
      |> Option.map (fn intro => intro OF map_filter class_elim sups);
    val class_intro = (#intro o AxClass.get_info thy) class;
    val raw_intro = case pred_intro'
     of SOME pred_intro => class_intro |> OF_LAST pred_intro
      | NONE => class_intro;
    val sort = Sign.super_classes thy class;
    val typ = TVar ((Name.aT, 0), sort);
    val defs = these_defs thy sups;
  in
    raw_intro
    |> Drule.instantiate' [SOME (Thm.ctyp_of thy typ)] []
    |> strip_all_ofclass thy sort
    |> Thm.strip_shyps
    |> MetaSimplifier.rewrite_rule defs
    |> Drule.unconstrainTs
  end;

fun class_interpretation class facts defs thy =
  let
    val params = these_params thy [class];
    val inst = (#inst o the_class_data thy) class;
    val tac = ALLGOALS (ProofContext.fact_tac facts);
    val prfx = class_prefix class;
  in
    thy
    |> fold_map (get_remove_global_constraint o fst o snd) params
    ||> prove_interpretation tac ((false, prfx), []) (Locale.Locale class)
          (inst, map (fn def => (("", []), def)) defs)
    |-> (fn cs => fold (Sign.add_const_constraint o apsnd SOME) cs)
  end;

fun intro_classes_tac facts st =
  let
    val thy = Thm.theory_of_thm st;
    val classes = Sign.all_classes thy;
    val class_trivs = map (Thm.class_triv thy) classes;
    val class_intros = these_intros thy;
    val axclass_intros = map_filter (try (#intro o AxClass.get_info thy)) classes;
  in
    Method.intros_tac (class_trivs @ class_intros @ axclass_intros) facts st
  end;

fun default_intro_classes_tac [] = intro_classes_tac []
  | default_intro_classes_tac _ = no_tac;

fun default_tac rules ctxt facts =
  HEADGOAL (Method.some_rule_tac rules ctxt facts) ORELSE
    default_intro_classes_tac facts;

val _ = Context.add_setup (Method.add_methods
 [("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of classes"),
  ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac),
    "apply some intro/elim rule")]);

fun subclass_rule thy (sub, sup) =
  let
    val ctxt = Locale.init sub thy;
    val ctxt_thy = ProofContext.init thy;
    val props =
      Locale.global_asms_of thy sup
      |> maps snd
      |> map (ObjectLogic.ensure_propT thy);
    fun tac { prems, context } =
      Locale.intro_locales_tac true context prems
        ORELSE ALLGOALS assume_tac;
  in
    Goal.prove_multi ctxt [] [] props tac
    |> map (Assumption.export false ctxt ctxt_thy)
    |> Variable.export ctxt ctxt_thy
  end;

fun prove_single_subclass (sub, sup) thms ctxt thy =
  let
    val ctxt_thy = ProofContext.init thy;
    val subclass_rule = Conjunction.intr_balanced thms
      |> Assumption.export false ctxt ctxt_thy
      |> singleton (Variable.export ctxt ctxt_thy);
    val sub_inst = Thm.ctyp_of thy (TVar ((Name.aT, 0), [sub]));
    val sub_ax = #axioms (AxClass.get_info thy sub);
    val classrel =
      #intro (AxClass.get_info thy sup)
      |> Drule.instantiate' [SOME sub_inst] []
      |> OF_LAST (subclass_rule OF sub_ax)
      |> strip_all_ofclass thy (Sign.super_classes thy sup)
      |> Thm.strip_shyps
  in
    thy
    |> AxClass.add_classrel classrel
    |> prove_interpretation_in (ALLGOALS (ProofContext.fact_tac thms))
         I (sub, Locale.Locale sup)
    |> ClassData.map (Graph.add_edge (sub, sup))
  end;

fun prove_subclass (sub, sup) thms ctxt thy =
  let
    val classes = ClassData.get thy;
    val is_sup = not o null o curry (Graph.irreducible_paths classes) sub;
    val supclasses = Graph.all_succs classes [sup] |> filter_out is_sup;
    fun transform sup' = subclass_rule thy (sup, sup') |> map (fn thm => thm OF thms);
  in
    thy
    |> fold_rev (fn sup' => prove_single_subclass (sub, sup')
         (transform sup') ctxt) supclasses
 end;


(** classes and class target **)

(* class context syntax *)

structure ClassSyntax = ProofDataFun(
  type T = {
    local_constraints: (string * typ) list,
    global_constraints: (string * typ) list,
    base_sort: sort,
    operations: (string * (typ * term)) list,
    unchecks: (term * term) list,
    passed: bool
  };
  fun init _ = {
    local_constraints = [],
    global_constraints = [],
    base_sort = [],
    operations = [],
    unchecks = [],
    passed = true
  };;
);

fun synchronize_syntax sups base_sort ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    fun subst_class_typ sort = map_atyps
      (fn TFree _ => TVar ((Name.aT, 0), sort) | ty' => ty');
    val operations = these_operations thy sups;
    val local_constraints =
      (map o apsnd) (subst_class_typ base_sort o fst o snd) operations;
    val global_constraints =
      (map o apsnd) (fn (class, (ty, _)) => subst_class_typ [class] ty) operations;
    fun declare_const (c, _) =
      let val b = Sign.base_name c
      in Sign.intern_const thy b = c ? Variable.declare_const (b, c) end;
    val unchecks = map (fn (c, (_, (ty, t))) => (t, Const (c, ty))) operations;
  in
    ctxt
    |> fold declare_const local_constraints
    |> fold (ProofContext.add_const_constraint o apsnd SOME) local_constraints
    |> ClassSyntax.put {
        local_constraints = local_constraints,
        global_constraints = global_constraints,
        base_sort = base_sort,
        operations = (map o apsnd) snd operations,
        unchecks = unchecks,
        passed = false
      }
  end;

fun refresh_syntax class ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val base_sort = (#base_sort o the_class_data thy) class;
  in synchronize_syntax [class] base_sort ctxt end;

val mark_passed = ClassSyntax.map
  (fn { local_constraints, global_constraints, base_sort, operations, unchecks, passed } =>
    { local_constraints = local_constraints, global_constraints = global_constraints,
      base_sort = base_sort, operations = operations, unchecks = unchecks, passed = true });

fun sort_term_check ts ctxt =
  let
    val { local_constraints, global_constraints, base_sort, operations, passed, ... } =
      ClassSyntax.get ctxt;
    fun check_improve (Const (c, ty)) = (case AList.lookup (op =) local_constraints c
         of SOME ty0 => (case try (Type.raw_match (ty0, ty)) Vartab.empty
             of SOME tyenv => (case Vartab.lookup tyenv (Name.aT, 0)
                 of SOME (_, TVar (tvar as (vi, _))) =>
                      if TypeInfer.is_param vi then cons tvar else I
                  | _ => I)
              | NONE => I)
          | NONE => I)
      | check_improve _ = I;
    val improvements = (fold o fold_aterms) check_improve ts [];
    val ts' = (map o map_types o map_atyps) (fn ty as TVar tvar =>
        if member (op =) improvements tvar
          then TFree (Name.aT, base_sort) else ty | ty => ty) ts;
    fun check t0 = Envir.expand_term (fn Const (c, ty) => (case AList.lookup (op =) operations c
         of SOME (ty0, t) =>
              if Type.typ_instance (ProofContext.tsig_of ctxt) (ty, ty0)
              then SOME (ty0, check t) else NONE
          | NONE => NONE)
      | _ => NONE) t0;
    val ts'' = map check ts';
  in if eq_list (op aconv) (ts, ts'') andalso passed then NONE
  else
    ctxt
    |> fold (ProofContext.add_const_constraint o apsnd SOME) global_constraints
    |> mark_passed
    |> pair ts''
    |> SOME
  end;

fun sort_term_uncheck ts ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val unchecks = (#unchecks o ClassSyntax.get) ctxt;
    val ts' = map (Pattern.rewrite_term thy unchecks []) ts;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', ctxt) end;

fun init_ctxt sups base_sort ctxt =
  ctxt
  |> Variable.declare_term
      (Logic.mk_type (TFree (Name.aT, base_sort)))
  |> synchronize_syntax sups base_sort
  |> Context.proof_map (
      Syntax.add_term_check 0 "class" sort_term_check
      #> Syntax.add_term_uncheck 0 "class" sort_term_uncheck)

fun init class thy =
  thy
  |> Locale.init class
  |> init_ctxt [class] ((#base_sort o the_class_data thy) class);


(* class definition *)

local

fun gen_class_spec prep_class prep_expr process_expr thy raw_supclasses raw_includes_elems =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val sups = filter (is_class thy) supclasses;
    fun the_base_sort class = lookup_class_data thy class
      |> Option.map #base_sort
      |> the_default [class];
    val base_sort = Sign.minimize_sort thy (maps the_base_sort supclasses);
    val supsort = Sign.minimize_sort thy supclasses;
    val suplocales = map Locale.Locale sups;
    val (raw_elems, includes) = fold_rev (fn Locale.Elem e => apfst (cons e)
      | Locale.Expr i => apsnd (cons (prep_expr thy i))) raw_includes_elems ([], []);
    val supexpr = Locale.Merge suplocales;
    val supparams = (map fst o Locale.parameters_of_expr thy) supexpr;
    val supconsts = AList.make (the o AList.lookup (op =) (these_params thy sups))
      (map fst supparams);
    val mergeexpr = Locale.Merge (suplocales @ includes);
    val constrain = Element.Constrains ((map o apsnd o map_atyps)
      (fn TFree (_, sort) => TFree (Name.aT, sort)) supparams);
  in
    ProofContext.init thy
    |> Locale.cert_expr supexpr [constrain]
    |> snd
    |> init_ctxt sups base_sort
    |> process_expr Locale.empty raw_elems
    |> fst
    |> (fn elems => ((((sups, supconsts), (supsort, base_sort, mergeexpr)),
          (*FIXME*) if null includes then constrain :: elems else elems)))
  end;

val read_class_spec = gen_class_spec Sign.intern_class Locale.intern_expr Locale.read_expr;
val check_class_spec = gen_class_spec (K I) (K I) Locale.cert_expr;

fun define_class_params (name, raw_superclasses) raw_consts raw_dep_axioms other_consts thy =
  let
    val superclasses = map (Sign.certify_class thy) raw_superclasses;
    val consts = (map o apfst o apsnd) (Sign.certify_typ thy) raw_consts;
    fun add_const ((c, ty), syn) =
      Sign.declare_const [] (c, Type.strip_sorts ty, syn) #>> Term.dest_Const;
    fun mk_axioms cs thy =
      raw_dep_axioms thy cs
      |> (map o apsnd o map) (Sign.cert_prop thy)
      |> rpair thy;
    fun constrain_typs class = (map o apsnd o Term.map_type_tfree)
      (fn (v, _) => TFree (v, [class]))
  in
    thy
    |> Sign.add_path (Logic.const_of_class name)
    |> fold_map add_const consts
    ||> Sign.restore_naming thy
    |-> (fn cs => mk_axioms cs
    #-> (fn axioms_prop => AxClass.define_class (name, superclasses)
           (map fst cs @ other_consts) axioms_prop
    #-> (fn class => `(fn _ => constrain_typs class cs)
    #-> (fn cs' => `(fn thy => AxClass.get_info thy class)
    #-> (fn {axioms, ...} => fold (Sign.add_const_constraint o apsnd SOME) cs'
    #> pair (class, (cs', axioms)))))))
  end;

fun gen_class prep_spec prep_param bname
    raw_supclasses raw_includes_elems raw_other_consts thy =
  let
    val class = Sign.full_name thy bname;
    val (((sups, supconsts), (supsort, base_sort, mergeexpr)), elems_syn) =
      prep_spec thy raw_supclasses raw_includes_elems;
    val other_consts = map (tap (Sign.the_const_type thy) o prep_param thy) raw_other_consts;
    fun mk_inst class cs =
      (map o apsnd o Term.map_type_tfree) (fn (v, _) => TFree (v, [class])) cs;
    fun fork_syntax (Element.Fixes xs) =
          fold_map (fn (c, ty, syn) => cons (c, syn) #> pair (c, ty, NoSyn)) xs
          #>> Element.Fixes
      | fork_syntax x = pair x;
    val (elems, global_syn) = fold_map fork_syntax elems_syn [];
    fun globalize (c, ty) =
      ((c, Term.map_type_tfree (K (TFree (Name.aT, base_sort))) ty),
        (the_default NoSyn o AList.lookup (op =) global_syn) c);
    fun extract_params thy =
      let
        val params = map fst (Locale.parameters_of thy class);
      in
        (params, (map globalize o snd o chop (length supconsts)) params)
      end;
    fun extract_assumes params thy cs =
      let
        val consts = supconsts @ (map (fst o fst) params ~~ cs);
        fun subst (Free (c, ty)) =
              Const ((fst o the o AList.lookup (op =) consts) c, ty)
          | subst t = t;
        fun prep_asm ((name, atts), ts) =
          ((Sign.base_name name, map (Attrib.attribute_i thy) atts),
            (map o map_aterms) subst ts);
      in
        Locale.global_asms_of thy class
        |> map prep_asm
      end;
  in
    thy
    |> Locale.add_locale_i (SOME "") bname mergeexpr elems
    |> snd
    |> ProofContext.theory_of
    |> `extract_params
    |-> (fn (all_params, params) =>
        define_class_params (bname, supsort) params
          (extract_assumes params) other_consts
      #-> (fn (_, (consts, axioms)) =>
        `(fn thy => class_intro thy class sups)
      #-> (fn class_intro =>
        PureThy.note_thmss_qualified "" (NameSpace.append class classN)
          [((introN, []), [([class_intro], [])])]
      #-> (fn [(_, [class_intro])] =>
        add_class_data ((class, sups),
          (map fst params ~~ consts, base_sort,
            mk_inst class (map snd supconsts @ consts),
              calculate_morphism class (supconsts @ (map (fst o fst) params ~~ consts)), class_intro))
      #> class_interpretation class axioms []
      ))))
    |> init class
    |> pair class
  end;

fun read_const thy = #1 o Term.dest_Const o ProofContext.read_const (ProofContext.init thy);

in

val class_cmd = gen_class read_class_spec read_const;
val class = gen_class check_class_spec (K I);

end; (*local*)


(* class target *)

fun logical_const class pos ((c, mx), dict) thy =
  let
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;
    val phi = morphism thy' class;

    val c' = Sign.full_name thy' c;
    val dict' = Morphism.term phi dict;
    val dict_def = map_types Logic.unvarifyT dict';
    val ty' = Term.fastype_of dict_def;
    val ty'' = Type.strip_sorts ty';
    val def_eq = Logic.mk_equals (Const (c', ty'), dict_def);
  in
    thy'
    |> Sign.declare_const pos (c, ty'', mx) |> snd
    |> Thm.add_def false false (c, def_eq)
    |>> Thm.symmetric
    |-> (fn def => class_interpretation class [def] [Thm.prop_of def]
          #> register_operation class (c', (dict', SOME (Thm.varifyT def))))
    |> Sign.restore_naming thy
    |> Sign.add_const_constraint (c', SOME ty')
  end;

fun syntactic_const class prmode pos ((c, mx), rhs) thy =
  let
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;
    val phi = morphism thy class;

    val c' = Sign.full_name thy' c;
    val rews = map (Logic.dest_equals o Thm.prop_of) (these_defs thy' [class])
    val rhs' = (Pattern.rewrite_term thy rews [] o Morphism.term phi) rhs;
    val ty' = Logic.unvarifyT (Term.fastype_of rhs');
  in
    thy'
    |> Sign.add_abbrev (#1 prmode) pos (c, map_types Type.strip_sorts rhs') |> snd
    |> Sign.add_const_constraint (c', SOME ty')
    |> Sign.notation true prmode [(Const (c', ty'), mx)]
    |> register_operation class (c', (rhs', NONE))
    |> Sign.restore_naming thy
  end;


(** instantiation target **)

(* bookkeeping *)

datatype instantiation = Instantiation of {
  arities: string list * sort list * sort,
  params: ((string * string) * (string * typ)) list
    (*(instantiation const, type constructor), (local instantiation parameter, typ)*)
}

structure Instantiation = ProofDataFun
(
  type T = instantiation
  fun init _ = Instantiation { arities = ([], [], []), params = [] };
);

fun mk_instantiation (arities, params) =
  Instantiation { arities = arities, params = params };
fun get_instantiation lthy = case Instantiation.get (LocalTheory.target_of lthy)
 of Instantiation data => data;
fun map_instantiation f = (LocalTheory.target o Instantiation.map)
  (fn Instantiation { arities, params } => mk_instantiation (f (arities, params)));

fun the_instantiation lthy = case get_instantiation lthy
 of { arities = ([], [], []), ... } => error "No instantiation target"
  | data => data;

val instantiation_params = #params o get_instantiation;

fun instantiation_param lthy v = instantiation_params lthy
  |> find_first (fn (_, (v', _)) => v = v')
  |> Option.map (fst o fst);

fun confirm_declaration c = (map_instantiation o apsnd)
  (filter_out (fn (_, (c', _)) => c' = c));


(* syntax *)

fun subst_param thy params = map_aterms (fn t as Const (c, ty) =>
    (case AxClass.inst_tyco_of thy (c, ty)
     of SOME tyco => (case AList.lookup (op =) params (c, tyco)
         of SOME v_ty => Free v_ty
          | NONE => t)
      | NONE => t)
  | t => t);

fun prep_spec lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val params = instantiation_params lthy;
  in subst_param thy params end;

fun inst_term_check ts lthy =
  let
    val params = instantiation_params lthy;
    val tsig = ProofContext.tsig_of lthy;
    val thy = ProofContext.theory_of lthy;

    fun check_improve (Const (c, ty)) = (case AxClass.inst_tyco_of thy (c, ty)
         of SOME tyco => (case AList.lookup (op =) params (c, tyco)
             of SOME (_, ty') => perhaps (try (Type.typ_match tsig (ty, ty')))
              | NONE => I)
          | NONE => I)
      | check_improve _ = I;
    val improvement = (fold o fold_aterms) check_improve ts Vartab.empty;
    val ts' = (map o map_types) (Envir.typ_subst_TVars improvement) ts;
    val ts'' = map (subst_param thy params) ts';
  in if eq_list (op aconv) (ts, ts'') then NONE else SOME (ts'', lthy) end;

fun inst_term_uncheck ts lthy =
  let
    val params = instantiation_params lthy;
    val ts' = (map o map_aterms) (fn t as Free (v, ty) =>
       (case get_first (fn ((c, _), (v', _)) => if v = v' then SOME c else NONE) params
         of SOME c => Const (c, ty)
          | NONE => t)
      | t => t) ts;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', lthy) end;


(* target *)

val sanatize_name = (*FIXME*)
  let
    fun is_valid s = Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s
      orelse s = "'" orelse s = "_";
    val is_junk = not o is_valid andf Symbol.is_regular;
    val junk = Scan.many is_junk;
    val scan_valids = Symbol.scanner "Malformed input"
      ((junk |--
        (Scan.optional (Scan.one Symbol.is_ascii_letter) "x" ^^ (Scan.many is_valid >> implode)
        --| junk))
      -- Scan.repeat ((Scan.many1 is_valid >> implode) --| junk) >> op ::);
  in
    explode #> scan_valids #> implode
  end;

fun init_instantiation (tycos, sorts, sort) thy =
  let
    val _ = if null tycos then error "At least one arity must be given" else ();
    val _ = map (the_class_data thy) sort;
    val vs = map TFree (Name.names Name.context Name.aT sorts);
    fun type_name "*" = "prod"
      | type_name "+" = "sum"
      | type_name s = sanatize_name (NameSpace.base s); (*FIXME*)
    fun get_param tyco (param, (c, ty)) = if can (AxClass.param_of_inst thy) (c, tyco)
      then NONE else SOME ((AxClass.unoverload_const thy (c, ty), tyco),
        (param ^ "_" ^ type_name tyco, map_atyps (K (Type (tyco, vs))) ty));
    val params = map_product get_param tycos (these_params thy sort) |> map_filter I;
  in
    thy
    |> ProofContext.init
    |> Instantiation.put (mk_instantiation ((tycos, sorts, sort), params))
    |> fold (Variable.declare_term o Logic.mk_type) vs
    |> fold (Variable.declare_names o Free o snd) params
    |> fold (fn tyco => ProofContext.add_arity (tyco, sorts, sort)) tycos
    |> Context.proof_map (
        Syntax.add_term_check 0 "instance" inst_term_check
        #> Syntax.add_term_uncheck 0 "instance" inst_term_uncheck)
  end;

fun gen_instantiation_instance do_proof after_qed lthy =
  let
    val (tycos, sorts, sort) = (#arities o the_instantiation) lthy;
    val arities_proof = maps (fn tyco => Logic.mk_arities (tyco, sorts, sort)) tycos;
    fun after_qed' results =
      LocalTheory.theory (fold (AxClass.add_arity o Thm.varifyT) results)
      #> after_qed;
  in
    lthy
    |> do_proof after_qed' arities_proof
  end;

val instantiation_instance = gen_instantiation_instance (fn after_qed => fn ts =>
  Proof.theorem_i NONE (after_qed o map the_single) (map (fn t => [(t, [])]) ts));

fun prove_instantiation_instance tac = gen_instantiation_instance (fn after_qed =>
  fn ts => fn lthy => after_qed (map (fn t => Goal.prove lthy [] [] t
    (fn {context, ...} => tac context)) ts) lthy) I;

fun conclude_instantiation lthy =
  let
    val { arities, params } = the_instantiation lthy;
    val (tycos, sorts, sort) = arities;
    val thy = ProofContext.theory_of lthy;
    val _ = map (fn tyco => if Sign.of_sort thy
        (Type (tyco, map TFree (Name.names Name.context Name.aT sorts)), sort)
      then () else error ("Missing instance proof for type " ^ quote (Sign.extern_type thy tyco)))
        tycos;
  in lthy end;

end;
