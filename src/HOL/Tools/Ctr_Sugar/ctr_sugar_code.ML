(*  Title:      HOL/Tools/Ctr_Sugar/ctr_sugar_code.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
    Copyright   2001-2013

Code generation for freely generated types.
*)

signature CTR_SUGAR_CODE =
sig
  val add_ctr_code: string -> typ list -> (string * typ) list -> thm list -> thm list -> thm list ->
    theory -> theory
end;

structure Ctr_Sugar_Code : CTR_SUGAR_CODE =
struct

open Ctr_Sugar_Util

val eqN = "eq"
val reflN = "refl"
val simpsN = "simps"

fun mk_case_certificate ctxt raw_thms =
  let
    val thms as thm1 :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Thm.unvarify_global (Proof_Context.theory_of ctxt)
      |> Conjunction.elim_balanced (length raw_thms)
      |> map Simpdata.mk_meta_eq
      |> map Drule.zero_var_indexes;
    val params = Term.add_free_names (Thm.prop_of thm1) [];
    val rhs = thm1
      |> Thm.prop_of |> Logic.dest_equals |> fst |> Term.strip_comb
      ||> fst o split_last |> list_comb;
    val lhs = Free (singleton (Name.variant_list params) "case", Term.fastype_of rhs);
    val assum = Thm.cterm_of ctxt (Logic.mk_equals (lhs, rhs));
  in
    thms
    |> Conjunction.intr_balanced
    |> rewrite_rule ctxt [Thm.symmetric (Thm.assume assum)]
    |> Thm.implies_intr assum
    |> Thm.generalize (Names.empty, Names.make_set params) 0
    |> Axclass.unoverload ctxt
    |> Thm.varifyT_global
  end;

fun mk_free_ctr_equations fcT ctrs inject_thms distinct_thms thy =
  let
    fun mk_fcT_eq (t, u) = Const (\<^const_name>\<open>HOL.equal\<close>, fcT --> fcT --> HOLogic.boolT) $ t $ u;
    fun true_eq tu = HOLogic.mk_eq (mk_fcT_eq tu, \<^term>\<open>True\<close>);
    fun false_eq tu = HOLogic.mk_eq (mk_fcT_eq tu, \<^term>\<open>False\<close>);

    val monomorphic_prop_of = Thm.prop_of o Thm.unvarify_global thy o Drule.zero_var_indexes;

    fun massage_inject (tp $ (eqv $ (_ $ t $ u) $ rhs)) = tp $ (eqv $ mk_fcT_eq (t, u) $ rhs);
    fun massage_distinct (tp $ (_ $ (_ $ t $ u))) = [tp $ false_eq (t, u), tp $ false_eq (u, t)];

    val triv_inject_goals =
      map_filter (fn c as (_, T) =>
          if T = fcT then SOME (HOLogic.mk_Trueprop (true_eq (Const c, Const c))) else NONE)
        ctrs;
    val inject_goals = map (massage_inject o monomorphic_prop_of) inject_thms;
    val distinct_goals = maps (massage_distinct o monomorphic_prop_of) distinct_thms;
    val refl_goal = HOLogic.mk_Trueprop (true_eq (Free ("x", fcT), Free ("x", fcT)));

    fun prove goal =
      Goal.prove_sorry_global thy [] [] goal (fn {context = ctxt, ...} =>
        HEADGOAL Goal.conjunction_tac THEN
        ALLGOALS (simp_tac
          (put_simpset HOL_basic_ss ctxt
            addsimps (map Simpdata.mk_eq (@{thms equal eq_True} @ inject_thms @ distinct_thms)))));

    fun proves goals = goals
      |> Logic.mk_conjunction_balanced
      |> prove
      |> Thm.close_derivation \<^here>
      |> Conjunction.elim_balanced (length goals)
      |> map Simpdata.mk_eq;
  in
    (proves (triv_inject_goals @ inject_goals @ distinct_goals), Simpdata.mk_eq (prove refl_goal))
  end;

fun add_equality fcT fcT_name As ctrs inject_thms distinct_thms =
  let
    fun add_def lthy =
      let
        fun mk_side const_name =
          Const (const_name, fcT --> fcT --> HOLogic.boolT) $ Free ("x", fcT) $ Free ("y", fcT);
        val spec =
          mk_Trueprop_eq (mk_side \<^const_name>\<open>HOL.equal\<close>, mk_side \<^const_name>\<open>HOL.eq\<close>)
          |> Syntax.check_term lthy;
        val ((_, (_, raw_def)), lthy') =
          Specification.definition NONE [] [] (Binding.empty_atts, spec) lthy;
        val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy');
        val def = singleton (Proof_Context.export lthy' thy_ctxt) raw_def;
      in
        (def, lthy')
      end;

    fun tac ctxt thms =
      Class.intro_classes_tac ctxt [] THEN ALLGOALS (Proof_Context.fact_tac ctxt thms);

    val qualify =
      Binding.qualify true (Long_Name.base_name fcT_name) o Binding.qualify true eqN o Binding.name;
  in
    Class.instantiation ([fcT_name], map dest_TFree As, [HOLogic.class_equal])
    #> add_def
    #-> Class.prove_instantiation_exit_result (map o Morphism.thm) tac o single
    #> snd
    #> `(mk_free_ctr_equations fcT ctrs inject_thms distinct_thms)
    #-> (fn (thms, thm) => Global_Theory.note_thmss Thm.theoremK
          [((qualify reflN, []), [([thm], [])]),
            ((qualify simpsN, []), [(rev thms, [])])])
    #-> (fn [(_, [thm]), (_, thms)] =>
          Code.declare_default_eqns_global ((thm, false) :: map (rpair true) thms))
  end;

fun add_ctr_code fcT_name raw_As raw_ctrs inject_thms distinct_thms case_thms thy =
  let
    val As = map (perhaps (try Logic.unvarifyT_global)) raw_As;
    val ctrs = map (apsnd (perhaps (try Logic.unvarifyT_global))) raw_ctrs;
    val fcT = Type (fcT_name, As);
    val unover_ctrs = map (fn ctr as (_, fcT) => (Axclass.unoverload_const thy ctr, fcT)) ctrs;
  in
    if can (Code.constrset_of_consts thy) unover_ctrs then
      thy
      |> Code.declare_datatype_global ctrs
      |> Code.declare_default_eqns_global (map (rpair true) (rev case_thms))
      |> Code.declare_case_global (mk_case_certificate (Proof_Context.init_global thy) case_thms)
      |> not (Sorts.has_instance (Sign.classes_of thy) fcT_name [HOLogic.class_equal])
        ? add_equality fcT fcT_name As ctrs inject_thms distinct_thms
    else
      thy
  end;

end;
