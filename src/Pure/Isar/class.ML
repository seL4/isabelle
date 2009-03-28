(*  Title:      Pure/Isar/ML
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales - interfaces.
*)

signature CLASS =
sig
  include CLASS_TARGET
    (*FIXME the split into class_target.ML, theory_target.ML and
      class.ML is artificial*)

  val class: binding -> class list -> Element.context_i list
    -> theory -> string * local_theory
  val class_cmd: binding -> xstring list -> Element.context list
    -> theory -> string * local_theory
  val prove_subclass: tactic -> class -> local_theory -> local_theory
  val subclass: class -> local_theory -> Proof.state
  val subclass_cmd: xstring -> local_theory -> Proof.state
end;

structure Class : CLASS =
struct

open Class_Target;

(** class definitions **)

local

(* calculating class-related rules including canonical interpretation *)

fun calculate thy class sups base_sort param_map assm_axiom =
  let
    val empty_ctxt = ProofContext.init thy;

    (* instantiation of canonical interpretation *)
    val aT = TFree (Name.aT, base_sort);
    val param_map_const = (map o apsnd) Const param_map;
    val param_map_inst = (map o apsnd)
      (Const o apsnd (map_atyps (K aT))) param_map;
    val const_morph = Element.inst_morphism thy
      (Symtab.empty, Symtab.make param_map_inst);
    val typ_morph = Element.inst_morphism thy
      (Symtab.empty |> Symtab.update (Name.aT, TFree (Name.aT, [class])), Symtab.empty);
    val (([raw_props], [(_, raw_inst_morph)], export_morph), _) = empty_ctxt
      |> Expression.cert_goal_expression ([(class, (("", false),
           Expression.Named param_map_const))], []);
    val (props, inst_morph) = if null param_map
      then (raw_props |> map (Morphism.term typ_morph),
        raw_inst_morph $> typ_morph)
      else (raw_props, raw_inst_morph); (*FIXME proper handling in
        locale.ML / expression.ML would be desirable*)

    (* witness for canonical interpretation *)
    val prop = try the_single props;
    val wit = Option.map (fn prop => let
        val sup_axioms = map_filter (fst o rules thy) sups;
        val loc_intro_tac = case Locale.intros_of thy class
          of (_, NONE) => all_tac
           | (_, SOME intro) => ALLGOALS (Tactic.rtac intro);
        val tac = loc_intro_tac
          THEN ALLGOALS (ProofContext.fact_tac (sup_axioms @ the_list assm_axiom))
      in Element.prove_witness empty_ctxt prop tac end) prop;
    val axiom = Option.map Element.conclude_witness wit;

    (* canonical interpretation *)
    val base_morph = inst_morph
      $> Morphism.binding_morphism (Binding.prefix false (class_prefix class))
      $> Element.satisfy_morphism (the_list wit);
    val defs = these_defs thy sups;
    val eq_morph = Element.eq_morphism thy defs;
    val morph = base_morph $> eq_morph;

    (* assm_intro *)
    fun prove_assm_intro thm =
      let
        val ((_, [thm']), _) = Variable.import_thms true [thm] empty_ctxt;
        val thm'' = Morphism.thm (const_morph $> eq_morph) thm';
        val tac = ALLGOALS (ProofContext.fact_tac [thm'']);
      in Goal.prove_global thy [] [] (Thm.prop_of thm'') (K tac) end;
    val assm_intro = Option.map prove_assm_intro
      (fst (Locale.intros_of thy class));

    (* of_class *)
    val of_class_prop_concl = Logic.mk_inclass (aT, class);
    val of_class_prop = case prop of NONE => of_class_prop_concl
      | SOME prop => Logic.mk_implies (Morphism.term const_morph
          ((map_types o map_atyps) (K aT) prop), of_class_prop_concl);
    val sup_of_classes = map (snd o rules thy) sups;
    val loc_axiom_intros = map Drule.standard' (Locale.axioms_of thy class);
    val axclass_intro = #intro (AxClass.get_info thy class);
    val base_sort_trivs = Drule.sort_triv thy (aT, base_sort);
    val tac = REPEAT (SOMEGOAL
      (Tactic.match_tac (axclass_intro :: sup_of_classes
         @ loc_axiom_intros @ base_sort_trivs)
           ORELSE' Tactic.assume_tac));
    val of_class = Goal.prove_global thy [] [] of_class_prop (K tac);

  in (base_morph, morph, export_morph, axiom, assm_intro, of_class) end;


(* reading and processing class specifications *)

fun prep_class_elems prep_decl thy supexpr sups proto_base_sort raw_elems =
  let

    (* user space type system: only permits 'a type variable, improves towards 'a *)
    val base_constraints = (map o apsnd)
      (map_type_tfree (K (TVar ((Name.aT, 0), proto_base_sort))) o fst o snd)
        (these_operations thy sups);
    val reject_bcd_etc = (map o map_atyps) (fn T as TFree (v, sort) =>
          if v = Name.aT then T
          else error ("No type variable other than " ^ Name.aT ^ " allowed in class specification")
      | T => T);
    fun singleton_fixate thy algebra Ts =
      let
        fun extract f = (fold o fold_atyps) f Ts [];
        val tfrees = extract
          (fn TFree (v, sort) => insert (op =) (v, sort) | _ => I);
        val inferred_sort = extract
          (fn TVar (_, sort) => curry (Sorts.inter_sort algebra) sort | _ => I);
        val fixate_sort = if null tfrees then inferred_sort
          else case tfrees
           of [(_, a_sort)] => if Sorts.sort_le algebra (a_sort, inferred_sort)
                then Sorts.inter_sort algebra (a_sort, inferred_sort)
                else error ("Type inference imposes additional sort constraint "
                  ^ Syntax.string_of_sort_global thy inferred_sort
                  ^ " of type parameter " ^ Name.aT ^ " of sort "
                  ^ Syntax.string_of_sort_global thy a_sort ^ ".")
            | _ => error "Multiple type variables in class specification.";
      in (map o map_atyps) (K (TFree (Name.aT, fixate_sort))) Ts end;
    fun add_typ_check level name f = Context.proof_map (Syntax.add_typ_check level name (fn xs => fn ctxt =>
      let val xs' = f xs in if eq_list (op =) (xs, xs') then NONE else SOME (xs', ctxt) end));

    (* preprocessing elements, retrieving base sort from type-checked elements *)
    val init_class_body = fold (ProofContext.add_const_constraint o apsnd SOME) base_constraints
      #> redeclare_operations thy sups
      #> add_typ_check 10 "reject_bcd_etc" reject_bcd_etc
      #> add_typ_check ~10 "singleton_fixate" (singleton_fixate thy (Sign.classes_of thy));
    val ((_, _, inferred_elems), _) = ProofContext.init thy
      |> prep_decl supexpr init_class_body raw_elems;
    fun fold_element_types f (Element.Fixes fxs) = fold (fn (_, SOME T, _) => f T) fxs
      | fold_element_types f (Element.Constrains cnstrs) = fold (f o snd) cnstrs
      | fold_element_types f (Element.Assumes assms) = fold (fold (fn (t, ts) =>
          fold_types f t #> (fold o fold_types) f ts) o snd) assms
      | fold_element_types f (Element.Defines _) =
          error ("\"defines\" element not allowed in class specification.")
      | fold_element_types f (Element.Notes _) =
          error ("\"notes\" element not allowed in class specification.");
    val base_sort = if null inferred_elems then proto_base_sort else
      case (fold o fold_element_types) Term.add_tfreesT inferred_elems []
       of [] => error "No type variable in class specification"
        | [(_, sort)] => sort
        | _ => error "Multiple type variables in class specification"

  in (base_sort, inferred_elems) end;

val cert_class_elems = prep_class_elems Expression.cert_declaration;
val read_class_elems = prep_class_elems Expression.cert_read_declaration;

fun prep_class_spec prep_class prep_class_elems thy raw_supclasses raw_elems =
  let

    (* prepare import *)
    val inter_sort = curry (Sorts.inter_sort (Sign.classes_of thy));
    val sups = map (prep_class thy) raw_supclasses
      |> Sign.minimize_sort thy;
    val _ = case filter_out (is_class thy) sups
     of [] => ()
      | no_classes => error ("No (proper) classes: " ^ commas (map quote no_classes));
    val supparams = (map o apsnd) (snd o snd) (these_params thy sups);
    val supparam_names = map fst supparams;
    val _ = if has_duplicates (op =) supparam_names
      then error ("Duplicate parameter(s) in superclasses: "
        ^ (commas o map quote o duplicates (op =)) supparam_names)
      else ();
    val supexpr = (map (fn sup => (sup, (("", false), Expression.Positional [])))
      sups, []);
    val given_basesort = fold inter_sort (map (base_sort thy) sups) [];

    (* infer types and base sort *)
    val (base_sort, inferred_elems) = prep_class_elems thy supexpr sups
      given_basesort raw_elems;
    val sup_sort = inter_sort base_sort sups

    (* process elements as class specification *)
    val class_ctxt = begin sups base_sort (ProofContext.init thy)
    val ((_, _, syntax_elems), _) = class_ctxt
      |> Expression.cert_declaration supexpr I inferred_elems;
    fun check_vars e vs = if null vs
      then error ("No type variable in part of specification element "
        ^ (Pretty.output o Pretty.chunks) (Element.pretty_ctxt class_ctxt e))
      else ();
    fun check_element (e as Element.Fixes fxs) =
          map (fn (_, SOME T, _) => check_vars e (Term.add_tfreesT T [])) fxs
      | check_element (e as Element.Assumes assms) =
          maps (fn (_, ts_pss) => map
            (fn (t, _) => check_vars e (Term.add_tfrees t [])) ts_pss) assms
      | check_element e = [()];
    val _ = map check_element syntax_elems;
    fun fork_syn (Element.Fixes xs) =
          fold_map (fn (c, ty, syn) => cons (c, syn) #> pair (c, ty, NoSyn)) xs
          #>> Element.Fixes
      | fork_syn x = pair x;
    val (elems, global_syntax) = fold_map fork_syn syntax_elems [];
    val constrain = Element.Constrains ((map o apsnd o map_atyps)
      (K (TFree (Name.aT, base_sort))) supparams);
      (*FIXME perhaps better: control type variable by explicit
      parameter instantiation of import expression*)

  in (((sups, supparam_names), (sup_sort, base_sort, supexpr)), (constrain :: elems, global_syntax)) end;

val cert_class_spec = prep_class_spec (K I) cert_class_elems;
val read_class_spec = prep_class_spec Sign.intern_class read_class_elems;


(* class establishment *)

fun add_consts class base_sort sups supparams global_syntax thy =
  let
    (*FIXME simplify*)
    val supconsts = supparams
      |> AList.make (snd o the o AList.lookup (op =) (these_params thy sups))
      |> (map o apsnd o apsnd o map_atyps o K o TFree) (Name.aT, [class]);
    val all_params = Locale.params_of thy class;
    val raw_params = (snd o chop (length supparams)) all_params;
    fun add_const ((raw_c, raw_ty), _) thy =
      let
        val b = Binding.name raw_c;
        val c = Sign.full_name thy b;
        val ty = map_atyps (K (TFree (Name.aT, base_sort))) raw_ty;
        val ty0 = Type.strip_sorts ty;
        val ty' = map_atyps (K (TFree (Name.aT, [class]))) ty0;
        val syn = (the_default NoSyn o AList.lookup Binding.eq_name global_syntax) b;
      in
        thy
        |> Sign.declare_const [] ((b, ty0), syn)
        |> snd
        |> pair ((Name.of_binding b, ty), (c, ty'))
      end;
  in
    thy
    |> Sign.add_path (class_prefix class)
    |> fold_map add_const raw_params
    ||> Sign.restore_naming thy
    |-> (fn params => pair (supconsts @ (map o apfst) fst params, params))
  end;

fun adjungate_axclass bname class base_sort sups supsort supparams global_syntax thy =
  let
    (*FIXME simplify*)
    fun globalize param_map = map_aterms
      (fn Free (v, ty) => Const ((fst o the o AList.lookup (op =) param_map) v, ty)
        | t => t);
    val raw_pred = Locale.intros_of thy class
      |> fst
      |> Option.map (Logic.unvarify o Logic.strip_imp_concl o Thm.prop_of);
    fun get_axiom thy = case (#axioms o AxClass.get_info thy) class
     of [] => NONE
      | [thm] => SOME thm;
  in
    thy
    |> add_consts class base_sort sups supparams global_syntax
    |-> (fn (param_map, params) => AxClass.define_class (bname, supsort)
          (map (fst o snd) params)
          [(Thm.empty_binding, Option.map (globalize param_map) raw_pred |> the_list)]
    #> snd
    #> `get_axiom
    #-> (fn assm_axiom => fold (Sign.add_const_constraint o apsnd SOME o snd) params
    #> pair (param_map, params, assm_axiom)))
  end;

fun gen_class prep_spec bname raw_supclasses raw_elems thy =
  let
    val class = Sign.full_name thy bname;
    val (((sups, supparams), (supsort, base_sort, supexpr)), (elems, global_syntax)) =
      prep_spec thy raw_supclasses raw_elems;
  in
    thy
    |> Expression.add_locale bname Binding.empty supexpr elems
    |> snd |> LocalTheory.exit_global
    |> adjungate_axclass bname class base_sort sups supsort supparams global_syntax
    |-> (fn (param_map, params, assm_axiom) =>
       `(fn thy => calculate thy class sups base_sort param_map assm_axiom)
    #-> (fn (base_morph, morph, export_morph, axiom, assm_intro, of_class) =>
       Locale.add_registration (class, (morph, export_morph))
    #> Locale.activate_global_facts (class, morph $> export_morph)
    #> register class sups params base_sort base_morph axiom assm_intro of_class))
    |> TheoryTarget.init (SOME class)
    |> pair class
  end;

in

val class = gen_class cert_class_spec;
val class_cmd = gen_class read_class_spec;

end; (*local*)


(** subclass relations **)

local

fun gen_subclass prep_class do_proof raw_sup lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val proto_sup = prep_class thy raw_sup;
    val proto_sub = case TheoryTarget.peek lthy
     of {is_class = false, ...} => error "Not in a class context"
      | {target, ...} => target;
    val (sub, sup) = AxClass.cert_classrel thy (proto_sub, proto_sup)

    val expr = ([(sup, (("", false), Expression.Positional []))], []);
    val (([props], deps, export), goal_ctxt) =
      Expression.cert_goal_expression expr lthy;
    val some_prop = try the_single props;
    val some_dep_morph = try the_single (map snd deps);
    fun after_qed some_wit =
      ProofContext.theory (register_subclass (sub, sup)
        some_dep_morph some_wit export)
      #> ProofContext.theory_of #> TheoryTarget.init (SOME sub);
  in do_proof after_qed some_prop goal_ctxt end;

fun user_proof after_qed some_prop =
  Element.witness_proof (after_qed o try the_single o the_single)
    [the_list some_prop];

fun tactic_proof tac after_qed some_prop ctxt =
  after_qed (Option.map
    (fn prop => Element.prove_witness ctxt prop tac) some_prop) ctxt;

in

val subclass = gen_subclass (K I) user_proof;
fun prove_subclass tac = gen_subclass (K I) (tactic_proof tac);
val subclass_cmd = gen_subclass Sign.read_class user_proof;

end; (*local*)

end;
