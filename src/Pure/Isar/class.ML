(*  Title:      Pure/Isar/ML
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales - interfaces
*)

signature CLASS =
sig
  include CLASS_TARGET
    (*FIXME the split into class_target.ML, theory_target.ML and
      class.ML is artificial*)

  val class: bstring -> class list -> Element.context_i list
    -> theory -> string * local_theory
  val class_cmd: bstring -> xstring list -> Element.context list
    -> theory -> string * local_theory
  val prove_subclass: tactic -> class -> local_theory -> local_theory
  val subclass: class -> local_theory -> Proof.state
  val subclass_cmd: xstring -> local_theory -> Proof.state
end;

structure Class : CLASS =
struct

open Class_Target;

(** rule calculation **)

fun calculate_axiom thy sups base_sort assm_axiom param_map class =
  case Locale.intros_of thy class
   of (_, NONE) => assm_axiom
    | (_, SOME intro) =>
      let
        fun instantiate thy sort = Thm.instantiate ([pairself (Thm.ctyp_of thy o TVar o pair (Name.aT, 0))
          (base_sort, sort)], map (fn (v, (c, ty)) => pairself (Thm.cterm_of thy)
            (Var ((v, 0), map_atyps (fn _ => TVar ((Name.aT, 0), sort)) ty),
              Const (c, map_atyps (fn _ => TVar ((Name.aT, 0), sort)) ty))) param_map);
        val axiom_premises = map_filter (fst o rules thy) sups
          @ the_list assm_axiom;
      in intro
        |> instantiate thy [class]
        |> (fn thm => thm OF axiom_premises)
        |> Drule.standard'
        |> Thm.close_derivation
        |> SOME
      end;

fun raw_morphism thy class sups param_map some_axiom =
  let
    val ctxt = ProofContext.init thy;
    val (([props], [(_, morph1)], export_morph), _) = ctxt
      |> Expression.cert_goal_expression ([(class, (("", false),
           Expression.Named ((map o apsnd) Const param_map)))], []);
    val morph2 = morph1
      $> Morphism.binding_morphism (Binding.add_prefix false (class_prefix class));
    val morph3 = case props
     of [prop] => morph2
          $> Element.satisfy_morphism [(Element.prove_witness ctxt prop
               (ALLGOALS (ProofContext.fact_tac (the_list some_axiom))))]
        | [] => morph2;
    (*FIXME generic amend operation for classes*)
    val morph4 = morph3 $> eq_morph thy (these_defs thy sups);
  in (morph4, export_morph) end;

fun calculate_rules thy morph sups base_sort param_map axiom class =
  let
    fun instantiate thy sort = Thm.instantiate ([pairself (Thm.ctyp_of thy o TVar o pair (Name.aT, 0))
      (base_sort, sort)], map (fn (v, (c, ty)) => pairself (Thm.cterm_of thy)
        (Var ((v, 0), map_atyps (fn _ => TVar ((Name.aT, 0), sort)) ty),
          Const (c, map_atyps (fn _ => TVar ((Name.aT, 0), sort)) ty))) param_map);
    val defs = these_defs thy sups;
    val assm_intro = Locale.intros_of thy class
      |> fst
      |> Option.map (instantiate thy base_sort)
      |> Option.map (MetaSimplifier.rewrite_rule defs)
      |> Option.map Thm.close_derivation;
    val fixate = Thm.instantiate
      (map (pairself (Thm.ctyp_of thy)) [(TVar ((Name.aT, 0), []), TFree (Name.aT, base_sort)),
        (TVar ((Name.aT, 0), base_sort), TFree (Name.aT, base_sort))], [])
    val of_class_sups = if null sups
      then map (fixate o Thm.class_triv thy) base_sort
      else map (fixate o snd o rules thy) sups;
    val locale_dests = map Drule.standard' (Locale.axioms_of thy class);
    val num_trivs = case length locale_dests
     of 0 => if is_none axiom then 0 else 1
      | n => n;
    val pred_trivs = if num_trivs = 0 then []
      else the axiom
        |> Thm.prop_of
        |> (map_types o map_atyps o K) (TFree (Name.aT, base_sort))
        |> (Thm.assume o Thm.cterm_of thy)
        |> replicate num_trivs;
    val axclass_intro = (#intro o AxClass.get_info thy) class;
    val of_class = (fixate axclass_intro OF of_class_sups OF locale_dests OF pred_trivs)
      |> Drule.standard'
      |> Thm.close_derivation;
  in (assm_intro, of_class) end;

fun note_assm_intro class assm_intro thy =
  thy
  |> Sign.sticky_prefix (class_prefix class ^ "_" ^ AxClass.axiomsN)
  |> PureThy.store_thm (AxClass.introN, assm_intro)
  |> snd
  |> Sign.restore_naming thy;


(** define classes **)

local

fun gen_class_spec prep_class process_decl thy raw_supclasses raw_elems =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val supsort = Sign.minimize_sort thy supclasses;
    val sups = filter (is_class thy) supsort;
    val base_sort = if null sups then supsort else
      foldr1 (Sorts.inter_sort (Sign.classes_of thy))
        (map (base_sort thy) sups);
    val supparams = (map o apsnd) (snd o snd) (these_params thy sups);
    val supparam_names = map fst supparams;
    val _ = if has_duplicates (op =) supparam_names
      then error ("Duplicate parameter(s) in superclasses: "
        ^ (commas o map quote o duplicates (op =)) supparam_names)
      else ();

    val supexpr = (map (fn sup => (sup, (("", false), Expression.Positional [])))
      sups, []);
    val constrain = Element.Constrains ((map o apsnd o map_atyps)
      (K (TFree (Name.aT, base_sort))) supparams);
      (*FIXME perhaps better: control type variable by explicit
      parameter instantiation of import expression*)
    val begin_ctxt = begin sups base_sort
      #> fold (Variable.declare_constraints o Free) ((map o apsnd o map_atyps)
          (K (TFree (Name.aT, base_sort))) supparams) (*FIXME
            should constraints be issued in begin?*)
    val ((_, _, syntax_elems), _) = ProofContext.init thy
      |> begin_ctxt
      |> process_decl supexpr raw_elems;
    fun fork_syn (Element.Fixes xs) =
          fold_map (fn (c, ty, syn) => cons (Binding.base_name c, syn) #> pair (c, ty, NoSyn)) xs
          #>> Element.Fixes
      | fork_syn x = pair x;
    val (elems, global_syntax) = fold_map fork_syn syntax_elems [];
  in (((sups, supparam_names), (supsort, base_sort, supexpr)), (constrain :: elems, global_syntax)) end;

val cert_class_spec = gen_class_spec (K I) Expression.cert_declaration;
val read_class_spec = gen_class_spec Sign.intern_class Expression.cert_read_declaration;

fun add_consts bname class base_sort sups supparams global_syntax thy =
  let
    val supconsts = supparams
      |> AList.make (snd o the o AList.lookup (op =) (these_params thy sups))
      |> (map o apsnd o apsnd o map_atyps o K o TFree) (Name.aT, [class]);
    val all_params = Locale.params_of thy class;
    val raw_params = (snd o chop (length supparams)) all_params;
    fun add_const (b, SOME raw_ty, _) thy =
      let
        val v = Binding.base_name b;
        val c = Sign.full_bname thy v;
        val ty = map_atyps (K (TFree (Name.aT, base_sort))) raw_ty;
        val ty0 = Type.strip_sorts ty;
        val ty' = map_atyps (K (TFree (Name.aT, [class]))) ty0;
        val syn = (the_default NoSyn o AList.lookup (op =) global_syntax) v;
      in
        thy
        |> Sign.declare_const [] ((Binding.name v, ty0), syn)
        |> snd
        |> pair ((v, ty), (c, ty'))
      end;
  in
    thy
    |> Sign.add_path (Logic.const_of_class bname)
    |> fold_map add_const raw_params
    ||> Sign.restore_naming thy
    |-> (fn params => pair (supconsts @ (map o apfst) fst params, params))
  end;

fun adjungate_axclass bname class base_sort sups supsort supparams global_syntax thy =
  let
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
    |> add_consts bname class base_sort sups supparams global_syntax
    |-> (fn (param_map, params) => AxClass.define_class (bname, supsort)
          (map (fst o snd) params)
          [(((*Binding.name (bname ^ "_" ^ AxClass.axiomsN*) Binding.empty, []),
            Option.map (globalize param_map) raw_pred |> the_list)]
    #> snd
    #> `get_axiom
    #-> (fn assm_axiom => fold (Sign.add_const_constraint o apsnd SOME o snd) params
    #> pair (map (Const o snd) param_map, param_map, params, assm_axiom)))
  end;

fun gen_class prep_spec bname raw_supclasses raw_elems thy =
  let
    val class = Sign.full_bname thy bname;
    val (((sups, supparams), (supsort, base_sort, supexpr)), (elems, global_syntax)) =
      prep_spec thy raw_supclasses raw_elems;
    (*val export_morph = (*FIXME how canonical is this?*)
      Morphism.morphism { binding = I, var = I,
        typ = Logic.varifyT,
        term = (*map_types Logic.varifyT*) I,
        fact = map Thm.varifyT
      } $> Morphism.morphism { binding = I, var = I,
        typ = Logic.type_map TermSubst.zero_var_indexes,
        term = TermSubst.zero_var_indexes,
        fact = Drule.zero_var_indexes_list o map Thm.strip_shyps
      };*)
  in
    thy
    |> Expression.add_locale bname "" supexpr elems
    |> snd |> LocalTheory.exit_global
    |> adjungate_axclass bname class base_sort sups supsort supparams global_syntax
    |-> (fn (inst, param_map, params, assm_axiom) =>
       `(fn thy => calculate_axiom thy sups base_sort assm_axiom param_map class)
    #-> (fn axiom =>
       `(fn thy => raw_morphism thy class sups param_map axiom)
    #-> (fn (morph, export_morph) => Locale.add_registration (class, (morph, export_morph))
    #>  Locale.activate_global_facts (class, morph $> export_morph)
    #> `(fn thy => calculate_rules thy morph sups base_sort param_map axiom class)
    #-> (fn (assm_intro, of_class) =>
        register class sups params base_sort inst
          morph axiom assm_intro of_class
    (*#> fold (note_assm_intro class) (the_list assm_intro*)))))
    |> TheoryTarget.init (SOME class)
    |> pair class
  end;

in

val class = gen_class cert_class_spec;
val class_cmd = gen_class read_class_spec;

end; (*local*)


(** subclass relations **)

local

fun prove_sublocale tac (sub, expr) =
  Expression.sublocale sub expr
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun gen_subclass prep_class do_proof raw_sup lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val sup = prep_class thy raw_sup;
    val sub = case TheoryTarget.peek lthy
     of {is_class = false, ...} => error "Not a class context"
      | {target, ...} => target;
    val _ = if Sign.subsort thy ([sup], [sub])
      then error ("Class " ^ Syntax.string_of_sort lthy [sup]
        ^ " is subclass of class " ^ Syntax.string_of_sort lthy [sub])
      else ();
    val sub_params = map fst (these_params thy [sub]);
    val sup_params = map fst (these_params thy [sup]);
    val err_params = subtract (op =) sub_params sup_params;
    val _ = if null err_params then [] else
      error ("Class " ^ Syntax.string_of_sort lthy [sub] ^ " lacks parameter(s) " ^
        commas_quote err_params ^ " of " ^ Syntax.string_of_sort lthy [sup]);

    val expr = ([(sup, (("", false), Expression.Positional []))], []);
    val (([props], _, _), goal_ctxt) =
      Expression.cert_goal_expression expr lthy;
    val some_prop = try the_single props; (*FIXME*)
    fun after_qed some_thm =
      LocalTheory.theory (register_subclass (sub, sup) some_thm)
      #> is_some some_thm ? LocalTheory.theory
        (prove_sublocale (ALLGOALS (ProofContext.fact_tac (the_list some_thm))) (sub, expr))
      #> (TheoryTarget.init (SOME sub) o ProofContext.theory_of);
  in
    do_proof after_qed some_prop lthy
  end;

fun user_proof after_qed NONE =
      Proof.theorem_i NONE (K (after_qed NONE)) [[]]
  | user_proof after_qed (SOME prop) =
      Proof.theorem_i NONE (after_qed o try the_single o the_single) [[(prop, [])]];

fun tactic_proof tac after_qed NONE lthy =
      after_qed NONE lthy
  | tactic_proof tac after_qed (SOME prop) lthy =
      after_qed (SOME (Goal.prove (LocalTheory.target_of lthy) [] [] prop
        (K tac))) lthy;

in

val subclass = gen_subclass (K I) user_proof;
fun prove_subclass tac = gen_subclass (K I) (tactic_proof tac);
val subclass_cmd = gen_subclass Sign.read_class user_proof;

end; (*local*)


end;

