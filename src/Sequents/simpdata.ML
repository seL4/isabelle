(*  Title:      Sequents/simpdata.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Instantiation of the generic simplifier for LK.

Borrows from the DC simplifier of Soren Heilmann.
*)


(** Conversion into rewrite rules **)

(*Make atomic rewrite rules*)
fun atomize r =
 case concl_of r of
   Const("Trueprop",_) $ Abs(_,_,a) $ Abs(_,_,c) =>
     (case (forms_of_seq a, forms_of_seq c) of
        ([], [p]) =>
          (case p of
               Const("imp",_)$_$_ => atomize(r RS @{thm mp_R})
             | Const("conj",_)$_$_   => atomize(r RS @{thm conjunct1}) @
                   atomize(r RS @{thm conjunct2})
             | Const("All",_)$_      => atomize(r RS @{thm spec})
             | Const("True",_)       => []    (*True is DELETED*)
             | Const("False",_)      => []    (*should False do something?*)
             | _                     => [r])
      | _ => [])  (*ignore theorem unless it has precisely one conclusion*)
 | _ => [r];

(*Make meta-equalities.*)
fun mk_meta_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | Const("Trueprop",_) $ Abs(_,_,a) $ Abs(_,_,c) =>
        (case (forms_of_seq a, forms_of_seq c) of
             ([], [p]) =>
                 (case p of
                      (Const("equal",_)$_$_)   => th RS @{thm eq_reflection}
                    | (Const("iff",_)$_$_) => th RS @{thm iff_reflection}
                    | (Const("Not",_)$_)      => th RS @{thm iff_reflection_F}
                    | _                       => th RS @{thm iff_reflection_T})
           | _ => error ("addsimps: unable to use theorem\n" ^
                         Display.string_of_thm_without_context th));

(*Replace premises x=y, X<->Y by X==Y*)
val mk_meta_prems =
    rule_by_tactic
      (REPEAT_FIRST (resolve_tac [@{thm meta_eq_to_obj_eq}, @{thm def_imp_iff}]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong rl =
  standard(mk_meta_eq (mk_meta_prems rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must use =-equality or <->");


(*** Standard simpsets ***)

val triv_rls = [@{thm FalseL}, @{thm TrueR}, @{thm basic}, @{thm refl},
  @{thm iff_refl}, reflexive_thm];

fun unsafe_solver prems =
  FIRST' [resolve_tac (triv_rls @ prems), assume_tac];

(*No premature instantiation of variables during simplification*)
fun safe_solver prems =
 FIRST' [fn i => DETERM (match_tac (triv_rls @ prems) i), eq_assume_tac];

(*No simprules, but basic infrastructure for simplification*)
val LK_basic_ss =
  Simplifier.theory_context @{theory} empty_ss
    setsubgoaler asm_simp_tac
    setSSolver (mk_solver "safe" safe_solver)
    setSolver (mk_solver "unsafe" unsafe_solver)
    setmksimps (map mk_meta_eq o atomize o gen_all)
    setmkcong mk_meta_cong;

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
  addeqcongs [@{thm left_cong}]
  addcongs [@{thm imp_cong}];

change_simpset (fn _ => LK_ss);
