(*  Title:      Pure/Isar/class_target.ML
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales - mechanisms.
*)

signature CLASS_TARGET =
sig
  (*classes*)
  val register: class -> class list -> ((string * typ) * (string * typ)) list
    -> sort -> term list -> morphism
    -> thm option -> thm option -> thm -> theory -> theory

  val begin: class list -> sort -> Proof.context -> Proof.context
  val init: class -> theory -> Proof.context
  val declare: class -> Properties.T
    -> (string * mixfix) * term -> theory -> theory
  val abbrev: class -> Syntax.mode -> Properties.T
    -> (string * mixfix) * term -> theory -> theory
  val refresh_syntax: class -> Proof.context -> Proof.context

  val intro_classes_tac: thm list -> tactic
  val default_intro_tac: Proof.context -> thm list -> tactic
  val prove_class_interpretation: class -> term list -> (class * string) list
    -> thm list -> thm list -> theory -> theory
  val prove_subclass_relation: class * class -> thm option -> theory -> theory

  val class_prefix: string -> string
  val is_class: theory -> class -> bool
  val these_params: theory -> sort -> (string * (class * (string * typ))) list
  val these_defs: theory -> sort -> thm list
  val base_sort: theory -> class -> sort
  val rules: theory -> class -> thm option * thm
  val print_classes: theory -> unit

  (*instances*)
  val init_instantiation: string list * (string * sort) list * sort
    -> theory -> local_theory
  val instantiation_instance: (local_theory -> local_theory)
    -> local_theory -> Proof.state
  val prove_instantiation_instance: (Proof.context -> tactic)
    -> local_theory -> local_theory
  val prove_instantiation_exit: (Proof.context -> tactic)
    -> local_theory -> theory
  val prove_instantiation_exit_result: (morphism -> 'a -> 'b)
    -> (Proof.context -> 'b -> tactic) -> 'a -> local_theory -> 'b * theory
  val conclude_instantiation: local_theory -> local_theory
  val instantiation_param: local_theory -> string -> string option
  val confirm_declaration: string -> local_theory -> local_theory
  val pretty_instantiation: local_theory -> Pretty.T
  val type_name: string -> string

  (*old axclass layer*)
  val axclass_cmd: bstring * xstring list
    -> (Attrib.binding * string list) list
    -> theory -> class * theory
  val classrel_cmd: xstring * xstring -> theory -> Proof.state

  (*old instance layer*)
  val instance_arity: (theory -> theory) -> arity -> theory -> Proof.state
  val instance_arity_cmd: bstring * xstring list * xstring -> theory -> Proof.state
end;

structure Class_Target : CLASS_TARGET =
struct

(*temporary adaption code to mediate between old and new locale code*)

structure Locale_Layer =
struct

val init = Old_Locale.init;
val parameters_of = Old_Locale.parameters_of;
val intros = Old_Locale.intros;
val dests = Old_Locale.dests;
val get_interpret_morph = Old_Locale.get_interpret_morph;
val Locale = Old_Locale.Locale;
val extern = Old_Locale.extern;
val intro_locales_tac = Old_Locale.intro_locales_tac;

fun prove_interpretation tac prfx_atts expr inst =
  Old_Locale.interpretation I prfx_atts expr inst
  ##> Proof.global_terminal_proof
      (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (tac ctxt), Position.none), NONE)
  ##> ProofContext.theory_of;

fun prove_interpretation_in tac after_qed (name, expr) =
  Old_Locale.interpretation_in_locale
      (ProofContext.theory after_qed) (name, expr)
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

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

  (* static part *)
  consts: (string * string) list
    (*locale parameter ~> constant name*),
  base_sort: sort,
  inst: term list
    (*canonical interpretation*),
  base_morph: Morphism.morphism
    (*static part of canonical morphism*),
  assm_intro: thm option,
  of_class: thm,
  axiom: thm option,
  
  (* dynamic part *)
  defs: thm list,
  operations: (string * (class * (typ * term))) list

};

fun rep_class_data (ClassData d) = d;
fun mk_class_data ((consts, base_sort, inst, base_morph, assm_intro, of_class, axiom),
    (defs, operations)) =
  ClassData { consts = consts, base_sort = base_sort, inst = inst,
    base_morph = base_morph, assm_intro = assm_intro, of_class = of_class, axiom = axiom,
    defs = defs, operations = operations };
fun map_class_data f (ClassData { consts, base_sort, inst, base_morph, assm_intro,
    of_class, axiom, defs, operations }) =
  mk_class_data (f ((consts, base_sort, inst, base_morph, assm_intro, of_class, axiom),
    (defs, operations)));
fun merge_class_data _ (ClassData { consts = consts,
    base_sort = base_sort, inst = inst, base_morph = base_morph, assm_intro = assm_intro,
    of_class = of_class, axiom = axiom, defs = defs1, operations = operations1 },
  ClassData { consts = _, base_sort = _, inst = _, base_morph = _, assm_intro = _,
    of_class = _, axiom = _, defs = defs2, operations = operations2 }) =
  mk_class_data ((consts, base_sort, inst, base_morph, assm_intro, of_class, axiom),
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

fun the_inst thy = #inst o the_class_data thy;

fun these_params thy =
  let
    fun params class =
      let
        val const_typs = (#params o AxClass.get_info thy) class;
        val const_names = (#consts o the_class_data thy) class;
      in
        (map o apsnd)
          (fn c => (class, (c, (the o AList.lookup (op =) const_typs) c))) const_names
      end;
  in maps params o ancestry thy end;

fun these_assm_intros thy =
  Graph.fold (fn (_, (data, _)) => fold (insert Thm.eq_thm)
    ((the_list o #assm_intro o rep_class_data) data)) (ClassData.get thy) [];

fun these_defs thy = maps (these o Option.map #defs o lookup_class_data thy) o ancestry thy;

fun these_operations thy =
  maps (#operations o the_class_data thy) o ancestry thy;

val base_sort = #base_sort oo the_class_data;

fun rules thy class = let
    val { axiom, of_class, ... } = the_class_data thy class
  in (axiom, of_class) end;

val class_prefix = Logic.const_of_class o Sign.base_name;

fun class_binding_morph class =
  Binding.map_prefix (K (Binding.add_prefix false (class_prefix class)));

fun morphism thy class =
  let
    val { base_morph, defs, ... } = the_class_data thy class;
  in
    base_morph 
    $> Morphism.term_morphism (MetaSimplifier.rewrite_term thy defs [])
    $> Morphism.thm_morphism (MetaSimplifier.rewrite_rule defs)
  end;

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
        ("locale: " ^ Locale_Layer.extern thy class) else NONE,
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

fun register class superclasses params base_sort inst morph
    axiom assm_intro of_class thy =
  let
    val operations = map (fn (v_ty as (_, ty), (c, _)) =>
      (c, (class, (ty, Free v_ty)))) params;
    val add_class = Graph.new_node (class,
        mk_class_data (((map o pairself) fst params, base_sort,
          inst, morph, assm_intro, of_class, axiom), ([], operations)))
      #> fold (curry Graph.add_edge class) superclasses;
  in ClassData.map add_class thy end;

fun register_operation class (c, (t, some_def)) thy =
  let
    val base_sort = base_sort thy class;
    val prep_typ = map_type_tfree
      (fn (v, sort) => if Name.aT = v
        then TFree (v, base_sort) else TVar ((v, 0), sort));
    val t' = map_types prep_typ t;
    val ty' = Term.fastype_of t';
  in
    thy
    |> (ClassData.map o Graph.map_node class o map_class_data o apsnd)
      (fn (defs, operations) =>
        (fold cons (the_list some_def) defs,
          (c, (class, (ty', t'))) :: operations))
  end;


(** tactics and methods **)

fun prove_class_interpretation class inst consts hyp_facts def_facts thy =
  let
    val constraints = map (fn (class, c) => map_atyps (K (TFree (Name.aT,
      [class]))) (Sign.the_const_type thy c)) consts;
    val no_constraints = map (map_atyps (K (TFree (Name.aT, [])))) constraints;
    fun add_constraint c T = Sign.add_const_constraint (c, SOME T);
    fun tac ctxt = ALLGOALS (ProofContext.fact_tac (hyp_facts @ def_facts)
      ORELSE' (fn n => SELECT_GOAL (Locale_Layer.intro_locales_tac false ctxt []) n));
    val prfx = class_prefix class;
  in
    thy
    |> fold2 add_constraint (map snd consts) no_constraints
    |> Locale_Layer.prove_interpretation tac (class_binding_morph class) (Locale_Layer.Locale class)
          (map SOME inst, map (pair (Attrib.empty_binding) o Thm.prop_of) def_facts)
    |> snd
    |> fold2 add_constraint (map snd consts) constraints
  end;

fun prove_subclass_relation (sub, sup) some_thm thy =
  let
    val of_class = (snd o rules thy) sup;
    val intro = case some_thm
     of SOME thm => Drule.standard' (of_class OF [Drule.standard' thm])
      | NONE => Thm.instantiate ([pairself (Thm.ctyp_of thy o TVar o pair (Name.aT, 0))
          ([], [sub])], []) of_class;
    val classrel = (intro OF (the_list o fst o rules thy) sub)
      |> Thm.close_derivation;
  in
    thy
    |> AxClass.add_classrel classrel
    |> Locale_Layer.prove_interpretation_in (ALLGOALS (ProofContext.fact_tac (the_list some_thm)))
         I (sub, Locale_Layer.Locale sup)
    |> ClassData.map (Graph.add_edge (sub, sup))
  end;

fun intro_classes_tac facts st =
  let
    val thy = Thm.theory_of_thm st;
    val classes = Sign.all_classes thy;
    val class_trivs = map (Thm.class_triv thy) classes;
    val class_intros = map_filter (try (#intro o AxClass.get_info thy)) classes;
    val assm_intros = these_assm_intros thy;
  in
    Method.intros_tac (class_trivs @ class_intros @ assm_intros) facts st
  end;

fun default_intro_tac ctxt [] =
      intro_classes_tac [] ORELSE Old_Locale.intro_locales_tac true ctxt [] ORELSE
      Locale.intro_locales_tac true ctxt []
  | default_intro_tac _ _ = no_tac;

fun default_tac rules ctxt facts =
  HEADGOAL (Method.some_rule_tac rules ctxt facts) ORELSE
    default_intro_tac ctxt facts;

val _ = Context.>> (Context.map_theory
  (Method.add_methods
   [("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
      "back-chain introduction rules of classes"),
    ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac),
      "apply some intro/elim rule")]));


(** classes and class target **)

(* class context syntax *)

fun synchronize_class_syntax sups base_sort ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val algebra = Sign.classes_of thy;
    val operations = these_operations thy sups;
    fun subst_class_typ sort = map_type_tfree (K (TVar ((Name.aT, 0), sort)));
    val primary_constraints =
      (map o apsnd) (subst_class_typ base_sort o fst o snd) operations;
    val secondary_constraints =
      (map o apsnd) (fn (class, (ty, _)) => subst_class_typ [class] ty) operations;
    fun declare_const (c, _) =
      let val b = Sign.base_name c
      in Sign.intern_const thy b = c ? Variable.declare_const (b, c) end;
    fun improve (c, ty) = (case AList.lookup (op =) primary_constraints c
     of SOME ty' => (case try (Type.raw_match (ty', ty)) Vartab.empty
         of SOME tyenv => (case Vartab.lookup tyenv (Name.aT, 0)
             of SOME (_, ty' as TVar (tvar as (vi, sort))) =>
                  if TypeInfer.is_param vi
                    andalso Sorts.sort_le algebra (base_sort, sort)
                      then SOME (ty', TFree (Name.aT, base_sort))
                      else NONE
              | _ => NONE)
          | NONE => NONE)
      | NONE => NONE)
    fun subst (c, ty) = Option.map snd (AList.lookup (op =) operations c);
    val unchecks = map (fn (c, (_, (ty, t))) => (t, Const (c, ty))) operations;
  in
    ctxt
    |> fold declare_const primary_constraints
    |> Overloading.map_improvable_syntax (K (((primary_constraints, secondary_constraints),
        (((improve, subst), true), unchecks)), false))
    |> Overloading.set_primary_constraints
  end;

fun refresh_syntax class ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val base_sort = base_sort thy class;
  in synchronize_class_syntax [class] base_sort ctxt end;

fun begin sups base_sort ctxt =
  ctxt
  |> Variable.declare_term
      (Logic.mk_type (TFree (Name.aT, base_sort)))
  |> synchronize_class_syntax sups base_sort
  |> Overloading.add_improvable_syntax;

fun init class thy =
  thy
  |> Locale_Layer.init class
  |> begin [class] (base_sort thy class);


(* class target *)

fun declare class pos ((c, mx), dict) thy =
  let
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;
    val morph = morphism thy' class;
    val inst = the_inst thy' class;
    val params = map (apsnd fst o snd) (these_params thy' [class]);

    val c' = Sign.full_bname thy' c;
    val dict' = Morphism.term morph dict;
    val ty' = Term.fastype_of dict';
    val ty'' = Type.strip_sorts ty';
    val def_eq = Logic.mk_equals (Const (c', ty'), dict');
    fun get_axiom thy = ((Thm.varifyT o Thm.axiom thy) c', thy);
  in
    thy'
    |> Sign.declare_const pos ((Binding.name c, ty''), mx) |> snd
    |> Thm.add_def false false (c, def_eq)
    |>> Thm.symmetric
    ||>> get_axiom
    |-> (fn (def, def') => prove_class_interpretation class inst params [] [def]
      #> register_operation class (c', (dict', SOME (Thm.symmetric def')))
      #> PureThy.store_thm (c ^ "_raw", def')
      #> snd)
    |> Sign.restore_naming thy
    |> Sign.add_const_constraint (c', SOME ty')
  end;

fun abbrev class prmode pos ((c, mx), rhs) thy =
  let
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;

    val unchecks = map (fn (c, (_, (ty, t))) => (t, Const (c, ty)))
      (these_operations thy [class]);
    val c' = Sign.full_bname thy' c;
    val rhs' = Pattern.rewrite_term thy unchecks [] rhs;
    val rhs'' = map_types Logic.varifyT rhs';
    val ty' = Term.fastype_of rhs';
  in
    thy'
    |> Sign.add_abbrev (#1 prmode) pos (Binding.name c, map_types Type.strip_sorts rhs'') |> snd
    |> Sign.add_const_constraint (c', SOME ty')
    |> Sign.notation true prmode [(Const (c', ty'), mx)]
    |> not (#1 prmode = PrintMode.input) ? register_operation class (c', (rhs', NONE))
    |> Sign.restore_naming thy
  end;


(** instantiation target **)

(* bookkeeping *)

datatype instantiation = Instantiation of {
  arities: string list * (string * sort) list * sort,
  params: ((string * string) * (string * typ)) list
    (*(instantiation parameter, type constructor), (local instantiation parameter, typ)*)
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


(* syntax *)

fun synchronize_inst_syntax ctxt =
  let
    val Instantiation { arities = (_, _, sort), params = params } = Instantiation.get ctxt;
    val thy = ProofContext.theory_of ctxt;
    fun subst (c, ty) = case AxClass.inst_tyco_of thy (c, ty)
         of SOME tyco => (case AList.lookup (op =) params (c, tyco)
             of SOME (v_ty as (_, ty)) => SOME (ty, Free v_ty)
              | NONE => NONE)
          | NONE => NONE;
    val unchecks =
      map (fn ((c, _), v_ty as (_, ty)) => (Free v_ty, Const (c, ty))) params;
  in
    ctxt
    |> Overloading.map_improvable_syntax
         (fn (((primary_constraints, _), (((improve, _), _), _)), _) =>
            (((primary_constraints, []), (((improve, subst), false), unchecks)), false))
  end;


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
      ::: Scan.repeat ((Scan.many1 is_valid >> implode) --| junk));
  in
    explode #> scan_valids #> implode
  end;

fun type_name "*" = "prod"
  | type_name "+" = "sum"
  | type_name s = sanatize_name (NameSpace.base s); (*FIXME*)

fun resort_terms pp algebra consts constraints ts =
  let
    fun matchings (Const (c_ty as (c, _))) = (case constraints c
         of NONE => I
          | SOME sorts => fold2 (curry (Sorts.meet_sort algebra))
              (Consts.typargs consts c_ty) sorts)
      | matchings _ = I
    val tvartab = (fold o fold_aterms) matchings ts Vartab.empty
      handle Sorts.CLASS_ERROR e => error (Sorts.class_error pp e);
    val inst = map_type_tvar
      (fn (vi, sort) => TVar (vi, the_default sort (Vartab.lookup tvartab vi)));
  in if Vartab.is_empty tvartab then NONE else SOME ((map o map_types) inst ts) end;

fun init_instantiation (tycos, vs, sort) thy =
  let
    val _ = if null tycos then error "At least one arity must be given" else ();
    val params = these_params thy sort;
    fun get_param tyco (param, (_, (c, ty))) = if can (AxClass.param_of_inst thy) (c, tyco)
      then NONE else SOME ((c, tyco),
        (param ^ "_" ^ type_name tyco, map_atyps (K (Type (tyco, map TFree vs))) ty));
    val inst_params = map_product get_param tycos params |> map_filter I;
    val primary_constraints = map (apsnd
      (map_atyps (K (TVar ((Name.aT, 0), [])))) o snd o snd) params;
    val pp = Syntax.pp_global thy;
    val algebra = Sign.classes_of thy
      |> fold (fn tyco => Sorts.add_arities pp
            (tyco, map (fn class => (class, map snd vs)) sort)) tycos;
    val consts = Sign.consts_of thy;
    val improve_constraints = AList.lookup (op =)
      (map (fn (_, (class, (c, _))) => (c, [[class]])) params);
    fun resort_check ts ctxt = case resort_terms pp algebra consts improve_constraints ts
     of NONE => NONE
      | SOME ts' => SOME (ts', ctxt);
    fun improve (c, ty) = case AxClass.inst_tyco_of thy (c, ty)
     of SOME tyco => (case AList.lookup (op =) inst_params (c, tyco)
         of SOME (_, ty') => if Type.raw_instance (ty', ty) then SOME (ty, ty') else NONE
          | NONE => NONE)
      | NONE => NONE;
  in
    thy
    |> ProofContext.init
    |> Instantiation.put (mk_instantiation ((tycos, vs, sort), inst_params))
    |> fold (Variable.declare_typ o TFree) vs
    |> fold (Variable.declare_names o Free o snd) inst_params
    |> (Overloading.map_improvable_syntax o apfst)
         (fn ((_, _), ((_, subst), unchecks)) =>
            ((primary_constraints, []), (((improve, K NONE), false), [])))
    |> Overloading.add_improvable_syntax
    |> Context.proof_map (Syntax.add_term_check 0 "resorting" resort_check)
    |> synchronize_inst_syntax
  end;

fun confirm_declaration c = (map_instantiation o apsnd)
  (filter_out (fn (_, (c', _)) => c' = c))
  #> LocalTheory.target synchronize_inst_syntax

fun gen_instantiation_instance do_proof after_qed lthy =
  let
    val (tycos, vs, sort) = (#arities o the_instantiation) lthy;
    val arities_proof = maps (fn tyco => Logic.mk_arities (tyco, map snd vs, sort)) tycos;
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

fun prove_instantiation_exit tac = prove_instantiation_instance tac
  #> LocalTheory.exit_global;

fun prove_instantiation_exit_result f tac x lthy =
  let
    val morph = ProofContext.export_morphism lthy
      (ProofContext.init (ProofContext.theory_of lthy));
    val y = f morph x;
  in
    lthy
    |> prove_instantiation_exit (fn ctxt => tac ctxt y)
    |> pair y
  end;

fun conclude_instantiation lthy =
  let
    val { arities, params } = the_instantiation lthy;
    val (tycos, vs, sort) = arities;
    val thy = ProofContext.theory_of lthy;
    val _ = map (fn tyco => if Sign.of_sort thy
        (Type (tyco, map TFree vs), sort)
      then () else error ("Missing instance proof for type " ^ quote (Sign.extern_type thy tyco)))
        tycos;
  in lthy end;

fun pretty_instantiation lthy =
  let
    val { arities, params } = the_instantiation lthy;
    val (tycos, vs, sort) = arities;
    val thy = ProofContext.theory_of lthy;
    fun pr_arity tyco = Syntax.pretty_arity lthy (tyco, map snd vs, sort);
    fun pr_param ((c, _), (v, ty)) =
      (Pretty.block o Pretty.breaks) [Pretty.str v, Pretty.str "==",
        (Pretty.str o Sign.extern_const thy) c, Pretty.str "::", Syntax.pretty_typ_global thy ty];
  in
    (Pretty.block o Pretty.fbreaks)
      (Pretty.str "instantiation" :: map pr_arity tycos @ map pr_param params)
  end;

end;

