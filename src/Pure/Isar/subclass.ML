(*  Title:      Pure/Isar/subclass.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Prove subclass relationship between type classes.
*)

signature SUBCLASS =
sig
  val subclass: class -> local_theory -> Proof.state
  val subclass_cmd: xstring -> local_theory -> Proof.state
  val prove_subclass: tactic -> class -> local_theory -> local_theory
end;

structure Subclass : SUBCLASS =
struct

(** auxiliary **)

fun prove_interpretation_in tac after_qed (name, expr) =
  Locale.interpretation_in_locale
      (ProofContext.theory after_qed) (name, expr)
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun OF_LAST thm1 thm2 =
  let
    val n = (length o Logic.strip_imp_prems o prop_of) thm2;
  in (thm1 RSN (n, thm2)) end;

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

fun subclass_rule thy (sub, sup) =
  let
    val ctxt = Locale.init sub thy;
    val ctxt_thy = ProofContext.init thy;
    val params = Class.these_params thy [sup];
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
  end;

fun prove_subclass (sub, sup) thms ctxt thy =
  let
    val supclasses = Sign.complete_sort thy [sup]
      |> filter_out (fn class => Sign.subsort thy ([sub], [class]));
    fun transform sup' = subclass_rule thy (sup, sup') |> map (fn thm => thm OF thms);
  in
    thy
    |> fold_rev (fn sup' => prove_single_subclass (sub, sup')
         (transform sup') ctxt) supclasses
 end;


(** subclassing **)

local

fun gen_subclass prep_class do_proof raw_sup lthy =
  let
    (*FIXME make more use of local context; drop redundancies*)
    val ctxt = LocalTheory.target_of lthy;
    val thy = ProofContext.theory_of ctxt;
    val sup = prep_class thy raw_sup;
    val sub = case TheoryTarget.peek lthy
     of {is_class = false, ...} => error "No class context"
      | {target, ...} => target;
    val sub_params = map fst (Class.these_params thy [sub]);
    val sup_params = map fst (Class.these_params thy [sup]);
    val err_params = subtract (op =) sub_params sup_params;
    val _ = if null err_params then [] else
      error ("Class " ^ Sign.string_of_sort thy [sub] ^ " lacks parameter(s) " ^
          commas_quote err_params ^ " of " ^ Sign.string_of_sort thy [sup]);
    val sublocale_prop =
      Locale.global_asms_of thy sup
      |> maps snd
      |> map (ObjectLogic.ensure_propT thy);
    fun after_qed thms =
      LocalTheory.theory (prove_subclass (sub, sup) thms ctxt)
      (*#> (fn lthy => LocalTheory.reinit lthy thy) FIXME does not work as expected*);
  in
    do_proof after_qed sublocale_prop lthy
  end;

fun user_proof after_qed props =
  Proof.theorem_i NONE (after_qed o the_single) [map (rpair []) props];

fun tactic_proof tac after_qed props lthy =
  after_qed (Goal.prove_multi (LocalTheory.target_of lthy) [] [] props
    (K tac)) lthy;

in

val subclass = gen_subclass (K I) user_proof;
val subclass_cmd = gen_subclass Sign.read_class user_proof;
fun prove_subclass tac = gen_subclass (K I) (tactic_proof tac);

end; (*local*)

end;
