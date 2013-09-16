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
  val mk_partial_elim_rules : local_theory ->
    Function_Common.function_result -> thm list list
end;

structure Function_Elims : FUNCTION_ELIMS =
struct

open Function_Lib
open Function_Common

(* Extracts a function and its arguments from a proposition that is
   either of the form "f x y z = ..." or, in case of function that
   returns a boolean, "f x y z" *)
fun dest_funprop (Const ("HOL.eq", _) $ lhs $ rhs) = (strip_comb lhs, rhs)
  | dest_funprop (Const ("HOL.Not", _) $ trm) = (strip_comb trm, @{term "False"})
  | dest_funprop trm = (strip_comb trm, @{term "True"});

local

fun propagate_tac i thm =
  let fun inspect eq = case eq of
              Const ("HOL.Trueprop",_) $ (Const ("HOL.eq",_) $ Free x $ t) =>
                  if Logic.occs (Free x, t) then raise Match else true
            | Const ("HOL.Trueprop",_) $ (Const ("HOL.eq",_) $ t $ Free x) =>
                  if Logic.occs (Free x, t) then raise Match else false
            | _ => raise Match;
      fun mk_eq thm = (if inspect (prop_of thm) then
                          [thm RS eq_reflection]
                      else
                          [Thm.symmetric (thm RS eq_reflection)])
                      handle Match => [];
      val ss = Simplifier.global_context (Thm.theory_of_thm thm) empty_ss
               |> Simplifier.set_mksimps (K mk_eq)
  in
    asm_lr_simp_tac ss i thm
  end;

val eqBoolI = @{lemma "!!P. P ==> P = True" "!!P. ~P ==> P = False" by iprover+}
val boolE = @{thms HOL.TrueE HOL.FalseE}
val boolD = @{lemma "!!P. True = P ==> P" "!!P. False = P ==> ~P" by iprover+}
val eqBool = @{thms HOL.eq_True HOL.eq_False HOL.not_False_eq_True HOL.not_True_eq_False}

fun bool_subst_tac ctxt i =
    REPEAT (EqSubst.eqsubst_asm_tac ctxt [1] eqBool i)
    THEN REPEAT (dresolve_tac boolD i)
    THEN REPEAT (eresolve_tac boolE i)

fun mk_bool_elims ctxt elim =
  let val tac = ALLGOALS (bool_subst_tac ctxt)
      fun mk_bool_elim b =
        elim
        |> Thm.forall_elim b
        |> Tactic.rule_by_tactic ctxt (TRY (resolve_tac eqBoolI 1))
        |> Tactic.rule_by_tactic ctxt tac
  in
      map mk_bool_elim [@{cterm True}, @{cterm False}]
  end;

in

fun mk_partial_elim_rules ctxt result=
  let val FunctionResult {fs, G, R, dom, psimps, simple_pinducts, cases,
                          termination, domintros, ...} = result;
      val n_fs = length fs;

      fun mk_partial_elim_rule (idx,f) =
        let fun mk_funeq 0 T (acc_vars, acc_lhs) =
                let val y = Free("y",T) in
                  (y :: acc_vars, (HOLogic.mk_Trueprop (HOLogic.mk_eq (acc_lhs, y))), T)
                end
              | mk_funeq n (Type("fun",[S,T])) (acc_vars, acc_lhs) =
                let val xn = Free ("x" ^ Int.toString n,S) in
                  mk_funeq (n - 1) T (xn :: acc_vars, acc_lhs $ xn)
                end
              | mk_funeq _ _ _ = raise (TERM ("Not a function.", [f]))

            val f_simps = filter (fn r => (prop_of r |> Logic.strip_assums_concl
                                           |> HOLogic.dest_Trueprop
                                           |> dest_funprop |> fst |> fst) = f)
                                 psimps

            val arity = hd f_simps |> prop_of |> Logic.strip_assums_concl
                                   |> HOLogic.dest_Trueprop
                                   |> snd o fst o dest_funprop |> length;
            val (free_vars,prop,ranT) = mk_funeq arity (fastype_of f) ([],f)
            val (rhs_var, arg_vars) = case free_vars of x::xs => (x, rev xs)
            val args = HOLogic.mk_tuple arg_vars;
            val domT = R |> dest_Free |> snd |> hd o snd o dest_Type

            val sumtree_inj = SumTree.mk_inj domT n_fs (idx+1) args;

            val thy = Proof_Context.theory_of ctxt;
            val cprop = cterm_of thy prop

            val asms = [cprop, cterm_of thy (HOLogic.mk_Trueprop (dom $ sumtree_inj))];
            val asms_thms = map Thm.assume asms;

            fun prep_subgoal i =
              REPEAT (eresolve_tac @{thms Pair_inject} i)
              THEN Method.insert_tac (case asms_thms of
                                        thm::thms => (thm RS sym) :: thms) i
              THEN propagate_tac i
              THEN TRY
                  ((EqSubst.eqsubst_asm_tac ctxt [1] psimps i) THEN atac i)
              THEN bool_subst_tac ctxt i;

          val tac = ALLGOALS prep_subgoal;

          val elim_stripped =
                nth cases idx
                |> Thm.forall_elim @{cterm "P::bool"}
                |> Thm.forall_elim (cterm_of thy args)
                |> Tactic.rule_by_tactic ctxt tac
                |> fold_rev Thm.implies_intr asms
                |> Thm.forall_intr (cterm_of thy rhs_var)

          val bool_elims = (case ranT of
                              Type ("HOL.bool", []) => mk_bool_elims ctxt elim_stripped
                              | _ => []);

          fun unstrip rl =
                rl  |> (fn thm => List.foldr (uncurry Thm.forall_intr) thm
                           (map (cterm_of thy) arg_vars))
                    |> Thm.forall_intr @{cterm "P::bool"}

      in
        map unstrip (elim_stripped :: bool_elims)
      end;

  in
    map_index mk_partial_elim_rule fs
  end;

end;

end;

