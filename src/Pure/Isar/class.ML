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
  case Old_Locale.intros thy class
   of (_, []) => assm_axiom
    | (_, [intro]) =>
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

fun raw_morphism thy class param_map some_axiom =
  let
    val ctxt = ProofContext.init thy;
    val some_wit = case some_axiom
     of SOME axiom => SOME (Element.prove_witness ctxt
          (Logic.unvarify (Thm.prop_of axiom))
            (ALLGOALS (ProofContext.fact_tac [axiom])))
      | NONE => NONE;
    val instT = Symtab.empty |> Symtab.update ("'a", TFree ("'a", [class]));
    val inst = Symtab.make ((map o apsnd) Const param_map);
  in case some_wit
   of SOME wit => Element.inst_morphism thy (instT, inst)
        $> Morphism.binding_morphism (Binding.add_prefix false (class_prefix class))
        $> Element.satisfy_morphism [wit]
    | NONE => Element.inst_morphism thy (instT, inst)
        $> Morphism.binding_morphism (Binding.add_prefix false (class_prefix class))
  end;

fun calculate_rules thy morph sups base_sort param_map axiom class =
  let
    fun instantiate thy sort = Thm.instantiate ([pairself (Thm.ctyp_of thy o TVar o pair (Name.aT, 0))
      (base_sort, sort)], map (fn (v, (c, ty)) => pairself (Thm.cterm_of thy)
        (Var ((v, 0), map_atyps (fn _ => TVar ((Name.aT, 0), sort)) ty),
          Const (c, map_atyps (fn _ => TVar ((Name.aT, 0), sort)) ty))) param_map);
    val defs = these_defs thy sups;
    val assm_intro = Old_Locale.intros thy class
      |> fst
      |> map (instantiate thy base_sort)
      |> map (MetaSimplifier.rewrite_rule defs)
      |> map Thm.close_derivation
      |> try the_single;
    val fixate = Thm.instantiate
      (map (pairself (Thm.ctyp_of thy)) [(TVar ((Name.aT, 0), []), TFree (Name.aT, base_sort)),
        (TVar ((Name.aT, 0), base_sort), TFree (Name.aT, base_sort))], [])
    val of_class_sups = if null sups
      then map (fixate o Thm.class_triv thy) base_sort
      else map (fixate o snd o rules thy) sups;
    val locale_dests = map Drule.standard' (Old_Locale.dests thy class);
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

fun gen_class_spec prep_class process_expr thy raw_supclasses raw_elems =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val supsort = Sign.minimize_sort thy supclasses;
    val sups = filter (is_class thy) supsort;
    val supparam_names = map fst (these_params thy sups);
    val _ = if has_duplicates (op =) supparam_names
      then error ("Duplicate parameter(s) in superclasses: "
        ^ (commas o map quote o duplicates (op =)) supparam_names)
      else ();
    val base_sort = if null sups then supsort else
      foldr1 (Sorts.inter_sort (Sign.classes_of thy))
        (map (base_sort thy) sups);
    val suplocales = map Old_Locale.Locale sups;
    val supexpr = Old_Locale.Merge suplocales;
    val supparams = (map fst o Old_Locale.parameters_of_expr thy) supexpr;
    val mergeexpr = Old_Locale.Merge suplocales;
    val constrain = Element.Constrains ((map o apsnd o map_atyps)
      (K (TFree (Name.aT, base_sort))) supparams);
    fun fork_syn (Element.Fixes xs) =
          fold_map (fn (c, ty, syn) => cons (Binding.base_name c, syn) #> pair (c, ty, NoSyn)) xs
          #>> Element.Fixes
      | fork_syn x = pair x;
    fun fork_syntax elems =
      let
        val (elems', global_syntax) = fold_map fork_syn elems [];
      in (constrain :: elems', global_syntax) end;
    val (elems, global_syntax) =
      ProofContext.init thy
      |> Old_Locale.cert_expr supexpr [constrain]
      |> snd
      |> begin sups base_sort
      |> process_expr Old_Locale.empty raw_elems
      |> fst
      |> fork_syntax
  in (((sups, supparams), (supsort, base_sort, mergeexpr)), (elems, global_syntax)) end;

val read_class_spec = gen_class_spec Sign.intern_class Old_Locale.read_expr;
val check_class_spec = gen_class_spec (K I) Old_Locale.cert_expr;

fun add_consts bname class base_sort sups supparams global_syntax thy =
  let
    val supconsts = map fst supparams
      |> AList.make (snd o the o AList.lookup (op =) (these_params thy sups))
      |> (map o apsnd o apsnd o map_atyps o K o TFree) (Name.aT, [class]);
    val all_params = map fst (Old_Locale.parameters_of thy class);
    val raw_params = (snd o chop (length supparams)) all_params;
    fun add_const (v, raw_ty) thy =
      let
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
    val raw_pred = Old_Locale.intros thy class
      |> fst
      |> map (Logic.unvarify o Logic.strip_imp_concl o Thm.prop_of);
    fun get_axiom thy = case (#axioms o AxClass.get_info thy) class
     of [] => NONE
      | [thm] => SOME thm;
  in
    thy
    |> add_consts bname class base_sort sups supparams global_syntax
    |-> (fn (param_map, params) => AxClass.define_class (bname, supsort)
          (map (fst o snd) params)
          [((Binding.name (bname ^ "_" ^ AxClass.axiomsN), []), map (globalize param_map) raw_pred)]
    #> snd
    #> `get_axiom
    #-> (fn assm_axiom => fold (Sign.add_const_constraint o apsnd SOME o snd) params
    #> pair (map (Const o snd) param_map, param_map, params, assm_axiom)))
  end;

fun gen_class prep_spec bname raw_supclasses raw_elems thy =
  let
    val class = Sign.full_bname thy bname;
    val (((sups, supparams), (supsort, base_sort, mergeexpr)), (elems, global_syntax)) =
      prep_spec thy raw_supclasses raw_elems;
    val supconsts = map (apsnd fst o snd) (these_params thy sups);
  in
    thy
    |> Old_Locale.add_locale "" bname mergeexpr elems
    |> snd
    |> ProofContext.theory_of
    |> adjungate_axclass bname class base_sort sups supsort supparams global_syntax
    |-> (fn (inst, param_map, params, assm_axiom) =>
        `(fn thy => calculate_axiom thy sups base_sort assm_axiom param_map class)
    #-> (fn axiom =>
        prove_class_interpretation class inst
          (supconsts @ map (pair class o fst o snd) params) (the_list axiom) []
    #> `(fn thy => raw_morphism thy class param_map axiom)
    #-> (fn morph =>
        `(fn thy => calculate_rules thy morph sups base_sort param_map axiom class)
    #-> (fn (assm_intro, of_class) =>
        register class sups params base_sort inst
          morph axiom assm_intro of_class
    #> fold (note_assm_intro class) (the_list assm_intro)))))
    |> TheoryTarget.init (SOME class)
    |> pair class
  end;

in

val class_cmd = gen_class read_class_spec;
val class = gen_class check_class_spec;

end; (*local*)


(** subclass relations **)

local

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
    val sublocale_prop =
      Old_Locale.global_asms_of thy sup
      |> maps snd
      |> try the_single
      |> Option.map (ObjectLogic.ensure_propT thy);
    fun after_qed some_thm =
      LocalTheory.theory (prove_subclass_relation (sub, sup) some_thm)
      #> (TheoryTarget.init (SOME sub) o ProofContext.theory_of);
  in
    do_proof after_qed sublocale_prop lthy
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

