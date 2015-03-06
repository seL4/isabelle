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

open Function_Lib
open Function_Common

(* Extract a function and its arguments from a proposition that is
   either of the form "f x y z = ..." or, in case of function that
   returns a boolean, "f x y z" *)
fun dest_funprop (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) = (strip_comb lhs, rhs)
  | dest_funprop (Const (@{const_name Not}, _) $ trm) = (strip_comb trm, @{term "False"})
  | dest_funprop trm = (strip_comb trm, @{term "True"});

local

fun propagate_tac ctxt i =
  let
    fun inspect eq =
      (case eq of
        Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ Free x $ t) =>
          if Logic.occs (Free x, t) then raise Match else true
      | Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ t $ Free x) =>
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

val eq_boolI = @{lemma "!!P. P ==> P = True" "!!P. ~P ==> P = False" by iprover+};
val boolE = @{thms HOL.TrueE HOL.FalseE};
val boolD = @{lemma "!!P. True = P ==> P" "!!P. False = P ==> ~P" by iprover+};
val eq_bool = @{thms HOL.eq_True HOL.eq_False HOL.not_False_eq_True HOL.not_True_eq_False};

fun bool_subst_tac ctxt i =
  REPEAT (EqSubst.eqsubst_asm_tac ctxt [1] eq_bool i)
  THEN REPEAT (dresolve_tac ctxt boolD i)
  THEN REPEAT (eresolve_tac ctxt boolE i)

fun mk_bool_elims ctxt elim =
  let
    val tac = ALLGOALS (bool_subst_tac ctxt);
    fun mk_bool_elim b =
      elim
      |> Thm.forall_elim b
      |> Tactic.rule_by_tactic ctxt (TRY (resolve_tac ctxt eq_boolI 1))
      |> Tactic.rule_by_tactic ctxt tac;
  in
    map mk_bool_elim [@{cterm True}, @{cterm False}]
  end;

in

fun mk_partial_elim_rules ctxt result =
  let
    val thy = Proof_Context.theory_of ctxt;

    val FunctionResult {fs, R, dom, psimps, cases, ...} = result;
    val n_fs = length fs;

    fun mk_partial_elim_rule (idx, f) =
      let
        fun mk_var x T ctxt = case Name.variant x ctxt of (x, ctxt) => (Free (x, T), ctxt)
        fun mk_funeq 0 T ctxt (acc_vars, acc_lhs) =
              let val (y, ctxt) = mk_var "y" T ctxt
              in  (y :: acc_vars, (HOLogic.mk_Trueprop (HOLogic.mk_eq (acc_lhs, y))), T, ctxt) end
          | mk_funeq n (Type (@{type_name "fun"}, [S, T])) ctxt (acc_vars, acc_lhs) =
              let val (xn, ctxt) = mk_var "x" S ctxt
              in  mk_funeq (n - 1) T ctxt (xn :: acc_vars, acc_lhs $ xn) end
          | mk_funeq _ _ _ _ = raise TERM ("Not a function.", [f]);

        val f_simps =
          filter (fn r =>
            (Thm.prop_of r |> Logic.strip_assums_concl
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
        val name_ctxt = Variable.names_of ctxt
        val (free_vars, prop, ranT, name_ctxt) = mk_funeq arity (fastype_of f) name_ctxt ([], f);
        val (rhs_var, arg_vars) = (case free_vars of x :: xs => (x, rev xs));
        val args = HOLogic.mk_tuple arg_vars;
        val domT = R |> dest_Free |> snd |> hd o snd o dest_Type;

        val P = mk_var "P" @{typ "bool"} name_ctxt |> fst |> Proof_Context.cterm_of ctxt
        val sumtree_inj = Sum_Tree.mk_inj domT n_fs (idx+1) args;

        val cprop = Proof_Context.cterm_of ctxt prop;

        val asms = [cprop, Proof_Context.cterm_of ctxt (HOLogic.mk_Trueprop (dom $ sumtree_inj))];
        val asms_thms = map Thm.assume asms;

        fun prep_subgoal_tac i =
          REPEAT (eresolve_tac ctxt @{thms Pair_inject} i)
          THEN Method.insert_tac (case asms_thms of thm :: thms => (thm RS sym) :: thms) i
          THEN propagate_tac ctxt i
          THEN TRY ((EqSubst.eqsubst_asm_tac ctxt [1] psimps i) THEN assume_tac ctxt i)
          THEN bool_subst_tac ctxt i;

        val elim_stripped =
          nth cases idx
          |> Thm.forall_elim P
          |> Thm.forall_elim (Proof_Context.cterm_of ctxt args)
          |> Tactic.rule_by_tactic ctxt (ALLGOALS prep_subgoal_tac)
          |> fold_rev Thm.implies_intr asms
          |> Thm.forall_intr (Proof_Context.cterm_of ctxt rhs_var);

        val bool_elims =
          (case ranT of
            Type (@{type_name bool}, []) => mk_bool_elims ctxt elim_stripped
          | _ => []);

        fun unstrip rl =
          rl
          |> fold_rev (Thm.forall_intr o Proof_Context.cterm_of ctxt) arg_vars
          |> Thm.forall_intr P
      in
        map unstrip (elim_stripped :: bool_elims)
      end;
  in
    map_index mk_partial_elim_rule fs
  end;

end;

end;
