(*  Title:      ZF/trancl.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Transitive closure of a relation
*)

Goal "bnd_mono(field(r)*field(r), %s. id(field(r)) Un (r O s))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, Un_mono, comp_mono] 2));
by (Blast_tac 1);
qed "rtrancl_bnd_mono";

Goalw [rtrancl_def] "r<=s ==> r^* <= s^*";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac [rtrancl_bnd_mono, subset_refl, id_mono,
		      comp_mono, Un_mono, field_mono, Sigma_mono] 1));
qed "rtrancl_mono";

(* r^* = id(field(r)) Un ( r O r^* )    *)
bind_thm ("rtrancl_unfold", rtrancl_bnd_mono RS (rtrancl_def RS def_lfp_unfold));

(** The relation rtrancl **)

(*  r^* <= field(r) * field(r)  *)
bind_thm ("rtrancl_type", rtrancl_def RS def_lfp_subset);

(*Reflexivity of rtrancl*)
Goal "[| a: field(r) |] ==> <a,a> : r^*";
by (resolve_tac [rtrancl_unfold RS ssubst] 1);
by (etac (idI RS UnI1) 1);
qed "rtrancl_refl";

(*Closure under composition with r  *)
Goal "[| <a,b> : r^*;  <b,c> : r |] ==> <a,c> : r^*";
by (resolve_tac [rtrancl_unfold RS ssubst] 1);
by (rtac (compI RS UnI2) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "rtrancl_into_rtrancl";

(*rtrancl of r contains all pairs in r  *)
Goal "<a,b> : r ==> <a,b> : r^*";
by (resolve_tac [rtrancl_refl RS rtrancl_into_rtrancl] 1);
by (REPEAT (ares_tac [fieldI1] 1));
qed "r_into_rtrancl";

(*The premise ensures that r consists entirely of pairs*)
Goal "r <= Sigma(A,B) ==> r <= r^*";
by (blast_tac (claset() addIs [r_into_rtrancl]) 1);
qed "r_subset_rtrancl";

Goal "field(r^*) = field(r)";
by (blast_tac (claset() addIs [r_into_rtrancl] 
                    addSDs [rtrancl_type RS subsetD]) 1);
qed "rtrancl_field";


(** standard induction rule **)

val major::prems = Goal
  "[| <a,b> : r^*; \
\     !!x. x: field(r) ==> P(<x,x>); \
\     !!x y z.[| P(<x,y>); <x,y>: r^*; <y,z>: r |]  ==>  P(<x,z>) |] \
\  ==>  P(<a,b>)";
by (rtac ([rtrancl_def, rtrancl_bnd_mono, major] MRS def_induct) 1);
by (blast_tac (claset() addIs prems) 1);
qed "rtrancl_full_induct";

(*nice induction rule.
  Tried adding the typing hypotheses y,z:field(r), but these
  caused expensive case splits!*)
val major::prems = Goal
  "[| <a,b> : r^*;                                              \
\     P(a);                                                     \
\     !!y z.[| <a,y> : r^*;  <y,z> : r;  P(y) |] ==> P(z)       \
\  |] ==> P(b)";
(*by induction on this formula*)
by (subgoal_tac "ALL y. <a,b> = <a,y> --> P(y)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (EVERY1 [etac (spec RS mp), rtac refl]);
(*now do the induction*)
by (resolve_tac [major RS rtrancl_full_induct] 1);
by (ALLGOALS (blast_tac (claset() addIs prems)));
qed "rtrancl_induct";

(*transitivity of transitive closure!! -- by induction.*)
Goalw [trans_def] "trans(r^*)";
by (REPEAT (resolve_tac [allI,impI] 1));
by (eres_inst_tac [("b","z")] rtrancl_induct 1);
by (DEPTH_SOLVE (eresolve_tac [asm_rl, rtrancl_into_rtrancl] 1));
qed "trans_rtrancl";

bind_thm ("rtrancl_trans", trans_rtrancl RS transD);

(*elimination of rtrancl -- by induction on a special formula*)
val major::prems = Goal
    "[| <a,b> : r^*;  (a=b) ==> P;                       \
\       !!y.[| <a,y> : r^*;   <y,b> : r |] ==> P |]      \
\    ==> P";
by (subgoal_tac "a = b  | (EX y. <a,y> : r^* & <y,b> : r)" 1);
(*see HOL/trancl*)
by (rtac (major RS rtrancl_induct) 2);
by (ALLGOALS (fast_tac (claset() addSEs prems)));
qed "rtranclE";


(**** The relation trancl ****)

(*Transitivity of r^+ is proved by transitivity of r^*  *)
Goalw [trans_def,trancl_def] "trans(r^+)";
by (blast_tac (claset() addIs [rtrancl_into_rtrancl RS 
			      (trans_rtrancl RS transD RS compI)]) 1);
qed "trans_trancl";

bind_thm ("trancl_trans", trans_trancl RS transD);

(** Conversions between trancl and rtrancl **)

Goalw [trancl_def] "<a,b> : r^+ ==> <a,b> : r^*";
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed "trancl_into_rtrancl";

(*r^+ contains all pairs in r  *)
Goalw [trancl_def] "<a,b> : r ==> <a,b> : r^+";
by (blast_tac (claset() addSIs [rtrancl_refl]) 1);
qed "r_into_trancl";

(*The premise ensures that r consists entirely of pairs*)
Goal "r <= Sigma(A,B) ==> r <= r^+";
by (blast_tac (claset() addIs [r_into_trancl]) 1);
qed "r_subset_trancl";

(*intro rule by definition: from r^* and r  *)
Goalw [trancl_def] "[| <a,b> : r^*;  <b,c> : r |]   ==>  <a,c> : r^+";
by (Blast_tac 1);
qed "rtrancl_into_trancl1";

(*intro rule from r and r^*  *)
val prems = goal (the_context ())
    "[| <a,b> : r;  <b,c> : r^* |]   ==>  <a,c> : r^+";
by (resolve_tac (prems RL [rtrancl_induct]) 1);
by (resolve_tac (prems RL [r_into_trancl]) 1);
by (etac trancl_trans 1);
by (etac r_into_trancl 1);
qed "rtrancl_into_trancl2";

(*Nice induction rule for trancl*)
val major::prems = Goal
  "[| <a,b> : r^+;                                      \
\     !!y.  [| <a,y> : r |] ==> P(y);                   \
\     !!y z.[| <a,y> : r^+;  <y,z> : r;  P(y) |] ==> P(z)       \
\  |] ==> P(b)";
by (rtac (rewrite_rule [trancl_def] major  RS  compEpair) 1);
(*by induction on this formula*)
by (subgoal_tac "ALL z. <y,z> : r --> P(z)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (Blast_tac 1);
by (etac rtrancl_induct 1);
by (ALLGOALS (fast_tac (claset() addIs (rtrancl_into_trancl1::prems))));
qed "trancl_induct";

(*elimination of r^+ -- NOT an induction rule*)
val major::prems = Goal
    "[| <a,b> : r^+;  \
\       <a,b> : r ==> P; \
\       !!y.[| <a,y> : r^+; <y,b> : r |] ==> P  \
\    |] ==> P";
by (subgoal_tac "<a,b> : r | (EX y. <a,y> : r^+  &  <y,b> : r)" 1);
by (fast_tac (claset() addIs prems) 1);
by (rtac (rewrite_rule [trancl_def] major RS compEpair) 1);
by (etac rtranclE 1);
by (ALLGOALS (blast_tac (claset() addIs [rtrancl_into_trancl1])));
qed "tranclE";

Goalw [trancl_def] "r^+ <= field(r)*field(r)";
by (blast_tac (claset() addEs [rtrancl_type RS subsetD RS SigmaE2]) 1);
qed "trancl_type";

Goalw [trancl_def] "r<=s ==> r^+ <= s^+";
by (REPEAT (ares_tac [comp_mono, rtrancl_mono] 1));
qed "trancl_mono";

(** Suggested by Sidi Ould Ehmety **)

Goal "(r^*)^* = r^*";
by (rtac equalityI 1);
by Auto_tac;
by (ALLGOALS (forward_tac [impOfSubs rtrancl_type]));
by (ALLGOALS Clarify_tac);
by (etac r_into_rtrancl 2);
by (etac rtrancl_induct 1);
by (asm_full_simp_tac (simpset() addsimps [rtrancl_refl, rtrancl_field]) 1);
by (blast_tac (claset() addIs [rtrancl_trans]) 1);
qed "rtrancl_idemp";
Addsimps [rtrancl_idemp];

Goal "[| R <= S; S <= R^* |] ==> S^* = R^*";
by (dtac rtrancl_mono 1);
by (dtac rtrancl_mono 1);
by (ALLGOALS Asm_full_simp_tac);
by (Blast_tac 1);
qed "rtrancl_subset";

Goal "[| r<= Sigma(A,B); s<=Sigma(C,D) |] ==> (r^* Un s^*)^* = (r Un s)^*";
by (rtac rtrancl_subset 1);
by (blast_tac (claset() addDs [r_subset_rtrancl]) 1);
by (blast_tac (claset() addIs [rtrancl_mono RS subsetD]) 1);
qed "rtrancl_Un_rtrancl";

(*** "converse" laws by Sidi Ould Ehmety ***)

(** rtrancl **)

Goal "<x,y>:converse(r)^* ==> <x,y>:converse(r^*)";
by (rtac converseI 1);
by (forward_tac [rtrancl_type RS subsetD] 1);
by (etac rtrancl_induct 1);
by (blast_tac (claset() addIs [rtrancl_refl]) 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "rtrancl_converseD";

Goal "<x,y>:converse(r^*) ==> <x,y>:converse(r)^*";
by (dtac converseD 1);
by (forward_tac [rtrancl_type RS subsetD] 1);
by (etac rtrancl_induct 1);
by (blast_tac (claset() addIs [rtrancl_refl]) 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "rtrancl_converseI";

Goal "converse(r)^* = converse(r^*)";
by (safe_tac (claset() addSIs [equalityI]));
by (forward_tac [rtrancl_type RS subsetD] 1);
by (safe_tac (claset() addSDs [rtrancl_converseD] addSIs [rtrancl_converseI]));
qed "rtrancl_converse";

(** trancl **)

Goal "<a, b>:converse(r)^+ ==> <a, b>:converse(r^+)";
by (etac trancl_induct 1);
by (auto_tac (claset() addIs [r_into_trancl, trancl_trans], simpset()));
qed "trancl_converseD";

Goal "<x,y>:converse(r^+) ==> <x,y>:converse(r)^+";
by (dtac converseD 1);
by (etac trancl_induct 1);
by (auto_tac (claset() addIs [r_into_trancl, trancl_trans], simpset()));
qed "trancl_converseI";

Goal "converse(r)^+ = converse(r^+)";
by (safe_tac (claset() addSIs [equalityI]));
by (forward_tac [trancl_type RS subsetD] 1);
by (safe_tac (claset() addSDs [trancl_converseD] addSIs [trancl_converseI]));
qed "trancl_converse";

val major::prems = Goal 
"[| <a, b>:r^+; !!y. <y, b> :r ==> P(y); \
\     !!y z. [| <y, z> : r; <z, b> : r^+; P(z) |] ==> P(y) |] \
\      ==> P(a)";
by (cut_facts_tac [major] 1);
by (dtac converseI 1);
by (full_simp_tac (simpset() addsimps [trancl_converse RS sym]) 1);
by (etac trancl_induct 1);
by (auto_tac (claset() addIs prems, 
              simpset() addsimps [trancl_converse]));
qed "converse_trancl_induct";
