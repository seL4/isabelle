(*  Title: 	ZF/trancl.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For trancl.thy.  Transitive closure of a relation
*)

open Trancl;

goal Trancl.thy "bnd_mono(field(r)*field(r), %s. id(field(r)) Un (r O s))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, Un_mono, comp_mono] 2));
by (fast_tac comp_cs 1);
val rtrancl_bnd_mono = result();

val [prem] = goalw Trancl.thy [rtrancl_def] "r<=s ==> r^* <= s^*";
by (rtac lfp_mono 1);
by (REPEAT (resolve_tac [rtrancl_bnd_mono, prem, subset_refl, id_mono,
			 comp_mono, Un_mono, field_mono, Sigma_mono] 1));
val rtrancl_mono = result();

(* r^* = id(field(r)) Un ( r O r^* )    *)
val rtrancl_unfold = rtrancl_bnd_mono RS (rtrancl_def RS def_lfp_Tarski);

(** The relation rtrancl **)

val rtrancl_type = standard (rtrancl_def RS def_lfp_subset);

(*Reflexivity of rtrancl*)
val [prem] = goal Trancl.thy "[| a: field(r) |] ==> <a,a> : r^*";
by (resolve_tac [rtrancl_unfold RS ssubst] 1);
by (rtac (prem RS idI RS UnI1) 1);
val rtrancl_refl = result();

(*Closure under composition with r  *)
val prems = goal Trancl.thy
    "[| <a,b> : r^*;  <b,c> : r |] ==> <a,c> : r^*";
by (resolve_tac [rtrancl_unfold RS ssubst] 1);
by (rtac (compI RS UnI2) 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
val rtrancl_into_rtrancl = result();

(*rtrancl of r contains all pairs in r  *)
val prems = goal Trancl.thy "<a,b> : r ==> <a,b> : r^*";
by (resolve_tac [rtrancl_refl RS rtrancl_into_rtrancl] 1);
by (REPEAT (resolve_tac (prems@[fieldI1]) 1));
val r_into_rtrancl = result();

(*The premise ensures that r consists entirely of pairs*)
val prems = goal Trancl.thy "r <= Sigma(A,B) ==> r <= r^*";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addIs [r_into_rtrancl]) 1);
val r_subset_rtrancl = result();

goal Trancl.thy "field(r^*) = field(r)";
by (fast_tac (eq_cs addIs [r_into_rtrancl] 
		    addSDs [rtrancl_type RS subsetD]) 1);
val rtrancl_field = result();


(** standard induction rule **)

val major::prems = goal Trancl.thy
  "[| <a,b> : r^*; \
\     !!x. x: field(r) ==> P(<x,x>); \
\     !!x y z.[| P(<x,y>); <x,y>: r^*; <y,z>: r |]  ==>  P(<x,z>) |] \
\  ==>  P(<a,b>)";
by (rtac ([rtrancl_def, rtrancl_bnd_mono, major] MRS def_induct) 1);
by (fast_tac (ZF_cs addIs prems addSEs [idE,compE]) 1);
val rtrancl_full_induct = result();

(*nice induction rule.
  Tried adding the typing hypotheses y,z:field(r), but these
  caused expensive case splits!*)
val major::prems = goal Trancl.thy
  "[| <a,b> : r^*;   						\
\     P(a); 							\
\     !!y z.[| <a,y> : r^*;  <y,z> : r;  P(y) |] ==> P(z) 	\
\  |] ==> P(b)";
(*by induction on this formula*)
by (subgoal_tac "ALL y. <a,b> = <a,y> --> P(y)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (EVERY1 [etac (spec RS mp), rtac refl]);
(*now do the induction*)
by (resolve_tac [major RS rtrancl_full_induct] 1);
by (ALLGOALS (fast_tac (ZF_cs addIs prems)));
val rtrancl_induct = result();

(*transitivity of transitive closure!! -- by induction.*)
goalw Trancl.thy [trans_def] "trans(r^*)";
by (REPEAT (resolve_tac [allI,impI] 1));
by (eres_inst_tac [("b","z")] rtrancl_induct 1);
by (DEPTH_SOLVE (eresolve_tac [asm_rl, rtrancl_into_rtrancl] 1));
val trans_rtrancl = result();

(*elimination of rtrancl -- by induction on a special formula*)
val major::prems = goal Trancl.thy
    "[| <a,b> : r^*;  (a=b) ==> P;			 \
\	!!y.[| <a,y> : r^*;   <y,b> : r |] ==> P |]	 \
\    ==> P";
by (subgoal_tac "a = b  | (EX y. <a,y> : r^* & <y,b> : r)" 1);
(*see HOL/trancl*)
by (rtac (major RS rtrancl_induct) 2);
by (ALLGOALS (fast_tac (ZF_cs addSEs prems)));
val rtranclE = result();


(**** The relation trancl ****)

(*Transitivity of r^+ is proved by transitivity of r^*  *)
goalw Trancl.thy [trans_def,trancl_def] "trans(r^+)";
by (safe_tac comp_cs);
by (rtac (rtrancl_into_rtrancl RS (trans_rtrancl RS transD RS compI)) 1);
by (REPEAT (assume_tac 1));
val trans_trancl = result();

(** Conversions between trancl and rtrancl **)

val [major] = goalw Trancl.thy [trancl_def] "<a,b> : r^+ ==> <a,b> : r^*";
by (resolve_tac [major RS compEpair] 1);
by (REPEAT (ares_tac [rtrancl_into_rtrancl] 1));
val trancl_into_rtrancl = result();

(*r^+ contains all pairs in r  *)
val [prem] = goalw Trancl.thy [trancl_def] "<a,b> : r ==> <a,b> : r^+";
by (REPEAT (ares_tac [prem,compI,rtrancl_refl,fieldI1] 1));
val r_into_trancl = result();

(*The premise ensures that r consists entirely of pairs*)
val prems = goal Trancl.thy "r <= Sigma(A,B) ==> r <= r^+";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addIs [r_into_trancl]) 1);
val r_subset_trancl = result();

(*intro rule by definition: from r^* and r  *)
val prems = goalw Trancl.thy [trancl_def]
    "[| <a,b> : r^*;  <b,c> : r |]   ==>  <a,c> : r^+";
by (REPEAT (resolve_tac ([compI]@prems) 1));
val rtrancl_into_trancl1 = result();

(*intro rule from r and r^*  *)
val prems = goal Trancl.thy
    "[| <a,b> : r;  <b,c> : r^* |]   ==>  <a,c> : r^+";
by (resolve_tac (prems RL [rtrancl_induct]) 1);
by (resolve_tac (prems RL [r_into_trancl]) 1);
by (etac (trans_trancl RS transD) 1);
by (etac r_into_trancl 1);
val rtrancl_into_trancl2 = result();

(*Nice induction rule for trancl*)
val major::prems = goal Trancl.thy
  "[| <a,b> : r^+;    					\
\     !!y.  [| <a,y> : r |] ==> P(y); 			\
\     !!y z.[| <a,y> : r^+;  <y,z> : r;  P(y) |] ==> P(z) 	\
\  |] ==> P(b)";
by (rtac (rewrite_rule [trancl_def] major  RS  compEpair) 1);
(*by induction on this formula*)
by (subgoal_tac "ALL z. <y,z> : r --> P(z)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (fast_tac ZF_cs 1);
by (etac rtrancl_induct 1);
by (ALLGOALS (fast_tac (ZF_cs addIs (rtrancl_into_trancl1::prems))));
val trancl_induct = result();

(*elimination of r^+ -- NOT an induction rule*)
val major::prems = goal Trancl.thy
    "[| <a,b> : r^+;  \
\       <a,b> : r ==> P; \
\	!!y.[| <a,y> : r^+; <y,b> : r |] ==> P  \
\    |] ==> P";
by (subgoal_tac "<a,b> : r | (EX y. <a,y> : r^+  &  <y,b> : r)" 1);
by (fast_tac (ZF_cs addIs prems) 1);
by (rtac (rewrite_rule [trancl_def] major RS compEpair) 1);
by (etac rtranclE 1);
by (ALLGOALS (fast_tac (ZF_cs addIs [rtrancl_into_trancl1])));
val tranclE = result();

goalw Trancl.thy [trancl_def] "r^+ <= field(r)*field(r)";
by (fast_tac (ZF_cs addEs [compE, rtrancl_type RS subsetD RS SigmaE2]) 1);
val trancl_type = result();

val [prem] = goalw Trancl.thy [trancl_def] "r<=s ==> r^+ <= s^+";
by (REPEAT (resolve_tac [prem, comp_mono, rtrancl_mono] 1));
val trancl_mono = result();

