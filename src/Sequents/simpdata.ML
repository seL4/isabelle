(*  Title:      Sequents/simpdata.ML
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Instantiation of the generic simplifier for LK.

Borrows from the DC simplifier of Soren Heilmann.
*)


(** Conversion into rewrite rules **)

(*Make atomic rewrite rules*)
fun atomize r =
 case Thm.concl_of r of
   \<^Const_>\<open>Trueprop for \<open>Abs(_,_,a)\<close> \<open>Abs(_,_,c)\<close>\<close> =>
     (case (Cla.forms_of_seq a, Cla.forms_of_seq c) of
        ([], [p]) =>
          (case p of
               \<^Const_>\<open>imp for _ _\<close> => atomize(r RS @{thm mp_R})
             | \<^Const_>\<open>conj for _ _\<close> => atomize(r RS @{thm conjunct1}) @
                   atomize(r RS @{thm conjunct2})
             | \<^Const_>\<open>All _ for _\<close> => atomize(r RS @{thm spec})
             | \<^Const_>\<open>True\<close> => []    (*True is DELETED*)
             | \<^Const_>\<open>False\<close> => []    (*should False do something?*)
             | _                     => [r])
      | _ => [])  (*ignore theorem unless it has precisely one conclusion*)
 | _ => [r];

(*Make meta-equalities.*)
fun mk_meta_eq ctxt th = case Thm.concl_of th of
    \<^Const_>\<open>Pure.eq _ for _ _\<close> => th
  | \<^Const_>\<open>Trueprop for \<open>Abs(_,_,a)\<close> \<open>Abs(_,_,c)\<close>\<close> =>
        (case (Cla.forms_of_seq a, Cla.forms_of_seq c) of
             ([], [p]) =>
                 (case p of
                      \<^Const_>\<open>equal _ for _ _\<close> => th RS @{thm eq_reflection}
                    | \<^Const_>\<open>iff for _ _\<close> => th RS @{thm iff_reflection}
                    | \<^Const_>\<open>Not for _\<close> => th RS @{thm iff_reflection_F}
                    | _                       => th RS @{thm iff_reflection_T})
           | _ => error ("addsimps: unable to use theorem\n" ^ Thm.string_of_thm ctxt th));

(*Replace premises x=y, X<->Y by X==Y*)
fun mk_meta_prems ctxt =
    rule_by_tactic ctxt
      (REPEAT_FIRST (resolve_tac ctxt [@{thm meta_eq_to_obj_eq}, @{thm def_imp_iff}]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong ctxt rl =
  Drule.zero_var_indexes (mk_meta_eq ctxt (mk_meta_prems ctxt rl))
    handle THM _ =>
      error("Premises and conclusion of congruence rules must use =-equality or <->");


(*** Standard simpsets ***)

val triv_rls = [@{thm FalseL}, @{thm TrueR}, @{thm basic}, @{thm refl},
  @{thm iff_refl}, reflexive_thm];

fun unsafe_solver ctxt =
  FIRST' [resolve_tac ctxt (triv_rls @ Simplifier.prems_of ctxt), assume_tac ctxt];

(*No premature instantiation of variables during simplification*)
fun safe_solver ctxt =
  FIRST' [fn i => DETERM (match_tac ctxt (triv_rls @ Simplifier.prems_of ctxt) i),
    eq_assume_tac];

(*No simprules, but basic infrastructure for simplification*)
val LK_basic_ss =
  empty_simpset \<^context>
  setSSolver (mk_solver "safe" safe_solver)
  setSolver (mk_solver "unsafe" unsafe_solver)
  |> Simplifier.set_subgoaler asm_simp_tac
  |> Simplifier.set_mksimps (fn ctxt => map (mk_meta_eq ctxt) o atomize o Variable.gen_all ctxt)
  |> Simplifier.set_mkcong mk_meta_cong
  |> simpset_of;

val LK_simps =
   [@{thm triv_forall_equality}, (* prunes params *)
    @{thm refl} RS @{thm P_iff_T}] @
    @{thms conj_simps} @ @{thms disj_simps} @ @{thms not_simps} @
    @{thms imp_simps} @ @{thms iff_simps} @ @{thms quant_simps} @
    @{thms all_simps} @ @{thms ex_simps} @
    [@{thm de_Morgan_conj}, @{thm de_Morgan_disj}, @{thm imp_disj1}, @{thm imp_disj2}] @
    @{thms LK_extra_simps};

val LK_ss =
  put_simpset LK_basic_ss \<^context> addsimps LK_simps
  |> Simplifier.add_eqcong @{thm left_cong}
  |> Simplifier.add_cong @{thm imp_cong}
  |> simpset_of;

