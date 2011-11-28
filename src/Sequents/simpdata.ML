(*  Title:      Sequents/simpdata.ML
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Instantiation of the generic simplifier for LK.

Borrows from the DC simplifier of Soren Heilmann.
*)


(** Conversion into rewrite rules **)

(*Make atomic rewrite rules*)
fun atomize r =
 case concl_of r of
   Const(@{const_name Trueprop},_) $ Abs(_,_,a) $ Abs(_,_,c) =>
     (case (forms_of_seq a, forms_of_seq c) of
        ([], [p]) =>
          (case p of
               Const(@{const_name imp},_)$_$_ => atomize(r RS @{thm mp_R})
             | Const(@{const_name conj},_)$_$_   => atomize(r RS @{thm conjunct1}) @
                   atomize(r RS @{thm conjunct2})
             | Const(@{const_name All},_)$_      => atomize(r RS @{thm spec})
             | Const(@{const_name True},_)       => []    (*True is DELETED*)
             | Const(@{const_name False},_)      => []    (*should False do something?*)
             | _                     => [r])
      | _ => [])  (*ignore theorem unless it has precisely one conclusion*)
 | _ => [r];

(*Make meta-equalities.*)
fun mk_meta_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | Const(@{const_name Trueprop},_) $ Abs(_,_,a) $ Abs(_,_,c) =>
        (case (forms_of_seq a, forms_of_seq c) of
             ([], [p]) =>
                 (case p of
                      (Const(@{const_name equal},_)$_$_)   => th RS @{thm eq_reflection}
                    | (Const(@{const_name iff},_)$_$_) => th RS @{thm iff_reflection}
                    | (Const(@{const_name Not},_)$_)      => th RS @{thm iff_reflection_F}
                    | _                       => th RS @{thm iff_reflection_T})
           | _ => error ("addsimps: unable to use theorem\n" ^
                         Display.string_of_thm_without_context th));

(*Replace premises x=y, X<->Y by X==Y*)
fun mk_meta_prems ctxt =
    rule_by_tactic ctxt
      (REPEAT_FIRST (resolve_tac [@{thm meta_eq_to_obj_eq}, @{thm def_imp_iff}]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong ss rl =
  Drule.zero_var_indexes (mk_meta_eq (mk_meta_prems (Simplifier.the_context ss) rl))
    handle THM _ =>
      error("Premises and conclusion of congruence rules must use =-equality or <->");


(*** Standard simpsets ***)

val triv_rls = [@{thm FalseL}, @{thm TrueR}, @{thm basic}, @{thm refl},
  @{thm iff_refl}, reflexive_thm];

fun unsafe_solver ss =
  FIRST' [resolve_tac (triv_rls @ Simplifier.prems_of ss), assume_tac];

(*No premature instantiation of variables during simplification*)
fun safe_solver ss =
 FIRST' [fn i => DETERM (match_tac (triv_rls @ Simplifier.prems_of ss) i), eq_assume_tac];

(*No simprules, but basic infrastructure for simplification*)
val LK_basic_ss =
  Simplifier.global_context @{theory} empty_ss
  setSSolver (mk_solver "safe" safe_solver)
  setSolver (mk_solver "unsafe" unsafe_solver)
  |> Simplifier.set_subgoaler asm_simp_tac
  |> Simplifier.set_mksimps (K (map mk_meta_eq o atomize o gen_all))
  |> Simplifier.set_mkcong mk_meta_cong;

val LK_simps =
   [triv_forall_equality, (* prunes params *)
    @{thm refl} RS @{thm P_iff_T}] @
    @{thms conj_simps} @ @{thms disj_simps} @ @{thms not_simps} @
    @{thms imp_simps} @ @{thms iff_simps} @ @{thms quant_simps} @
    @{thms all_simps} @ @{thms ex_simps} @
    [@{thm de_Morgan_conj}, @{thm de_Morgan_disj}, @{thm imp_disj1}, @{thm imp_disj2}] @
    @{thms LK_extra_simps};

val LK_ss =
  LK_basic_ss addsimps LK_simps
  |> Simplifier.add_eqcong @{thm left_cong}
  |> Simplifier.add_cong @{thm imp_cong};

