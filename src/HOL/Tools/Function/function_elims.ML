(*  Title:      HOL/Tools/Function/function_elims.ML
    Author:     Manuel Eberl, TU Muenchen

Generate the pelims rules for a function. These are of the shape
[|f x y z = w; !!\<dots>. [|x = \<dots>; y = \<dots>; z = \<dots>; w = \<dots>|] ==> P; \<dots>|] ==> P
and are derived from the cases rule. There is at least one pelim rule for
each function (cf. mutually recursive functions)
There may be more than one pelim rule for a function in case of functions
that return a boolean. For such a function, e.g. P x, not only the normal
elim rule with the premise P x = z is generated, but also two additional
elim rules with P x resp. \<not>P x as premises.
*)

signature FUNCTION_ELIMS =
sig
  val dest_funprop : term -> (term * term list) * term
  val mk_partial_elim_rules : Proof.context ->
    Function_Common.function_result -> thm list list
end;

structure Function_Elims : FUNCTION_ELIMS =
struct

(* Extract a function and its arguments from a proposition that is
   either of the form "f x y z = ..." or, in case of function that
   returns a boolean, "f x y z" *)
fun dest_funprop (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ rhs) = (strip_comb lhs, rhs)
  | dest_funprop (Const (\<^const_name>\<open>Not\<close>, _) $ t) = (strip_comb t, \<^term>\<open>False\<close>)
  | dest_funprop t = (strip_comb t, \<^term>\<open>True\<close>);

local

fun propagate_tac ctxt i =
  let
    fun inspect eq =
      (case eq of
        Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ Free x $ t) =>
          if Logic.occs (Free x, t) then raise Match else true
      | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ Free x) =>
          if Logic.occs (Free x, t) then raise Match else false
      | _ => raise Match);
    fun mk_eq thm =
      (if inspect (Thm.prop_of thm) then [thm RS eq_reflection]
       else [Thm.symmetric (thm RS eq_reflection)])
      handle Match => [];
    val simpset =
      empty_simpset ctxt
      |> Simplifier.set_mksimps (K mk_eq);
  in
    asm_lr_simp_tac simpset i
  end;

val eq_boolI = @{lemma "\<And>P. P \<Longrightarrow> P = True" "\<And>P. \<not> P \<Longrightarrow> P = False" by iprover+};
val boolE = @{thms HOL.TrueE HOL.FalseE};
val boolD = @{lemma "\<And>P. True = P \<Longrightarrow> P" "\<And>P. False = P \<Longrightarrow> \<not> P" by iprover+};
val eq_bool = @{thms HOL.eq_True HOL.eq_False HOL.not_False_eq_True HOL.not_True_eq_False};

fun bool_subst_tac ctxt =
  TRY o REPEAT_ALL_NEW (EqSubst.eqsubst_asm_tac ctxt [1] eq_bool)
  THEN_ALL_NEW TRY o REPEAT_ALL_NEW (dresolve_tac ctxt boolD)
  THEN_ALL_NEW TRY o REPEAT_ALL_NEW (eresolve_tac ctxt boolE);

fun mk_bool_elims ctxt elim =
  let
    fun mk_bool_elim b =
      elim
      |> Thm.forall_elim b
      |> Tactic.rule_by_tactic ctxt (distinct_subgoals_tac THEN TRY (resolve_tac ctxt eq_boolI 1))
      |> Tactic.rule_by_tactic ctxt (distinct_subgoals_tac THEN ALLGOALS (bool_subst_tac ctxt));
  in
    map mk_bool_elim [\<^cterm>\<open>True\<close>, \<^cterm>\<open>False\<close>]
  end;

in

fun mk_partial_elim_rules ctxt result =
  let
    val Function_Common.FunctionResult {fs, R, dom, psimps, cases, ...} = result;
    val n_fs = length fs;

    fun variant_free used_term v =
      Free (singleton (Variable.variant_names (Variable.declare_names used_term ctxt)) v);

    fun mk_partial_elim_rule (idx, f) =
      let
        fun mk_funeq 0 T (acc_args, acc_lhs) =
              let val y = variant_free acc_lhs ("y", T)
              in (y, rev acc_args, HOLogic.mk_Trueprop (HOLogic.mk_eq (acc_lhs, y))) end
          | mk_funeq n (Type (\<^type_name>\<open>fun\<close>, [S, T])) (acc_args, acc_lhs) =
              let val x = variant_free acc_lhs ("x", S)
              in mk_funeq (n - 1) T (x :: acc_args, acc_lhs $ x) end
          | mk_funeq _ _ _ = raise TERM ("Not a function", [f]);

        val f_simps =
          filter (fn r =>
            (Thm.prop_of r
              |> Logic.strip_assums_concl
              |> HOLogic.dest_Trueprop
              |> dest_funprop |> fst |> fst) = f)
            psimps;

        val arity =
          hd f_simps
          |> Thm.prop_of
          |> Logic.strip_assums_concl
          |> HOLogic.dest_Trueprop
          |> snd o fst o dest_funprop
          |> length;

        val (rhs_var, arg_vars, prop) = mk_funeq arity (fastype_of f) ([], f);
        val args = HOLogic.mk_tuple arg_vars;
        val domT = hd (dest_Type_args (snd (dest_Free R)));

        val P = Thm.cterm_of ctxt (variant_free prop ("P", \<^typ>\<open>bool\<close>));
        val sumtree_inj = Sum_Tree.mk_inj domT n_fs (idx + 1) args;

        val cprop = Thm.cterm_of ctxt prop;

        val asms = [cprop, Thm.cterm_of ctxt (HOLogic.mk_Trueprop (dom $ sumtree_inj))];
        val asms_thms = map Thm.assume asms;

        val prep_subgoal_tac =
          TRY o REPEAT_ALL_NEW (eresolve_tac ctxt @{thms Pair_inject})
          THEN' Method.insert_tac ctxt 
            (case asms_thms of thm :: thms => (thm RS sym) :: thms)
          THEN' propagate_tac ctxt
          THEN_ALL_NEW
            ((TRY o (EqSubst.eqsubst_asm_tac ctxt [1] psimps THEN' assume_tac ctxt)))
          THEN_ALL_NEW bool_subst_tac ctxt;

        val elim_stripped =
          nth cases idx
          |> Thm.forall_elim P
          |> Thm.forall_elim (Thm.cterm_of ctxt args)
          |> Tactic.rule_by_tactic ctxt (distinct_subgoals_tac THEN ALLGOALS prep_subgoal_tac)
          |> fold_rev Thm.implies_intr asms
          |> Thm.forall_intr (Thm.cterm_of ctxt rhs_var);

        val bool_elims =
          if fastype_of rhs_var = \<^typ>\<open>bool\<close>
          then mk_bool_elims ctxt elim_stripped
          else [];

        fun unstrip rl =
          rl
          |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt) arg_vars
          |> Thm.forall_intr P
      in
        map (unstrip #> Thm.solve_constraints) (elim_stripped :: bool_elims)
      end;
  in
    map_index mk_partial_elim_rule fs
  end;

end;

end;
