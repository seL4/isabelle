(*  Title:      CCL/trancl
    ID:         $Id$

For trancl.thy.

Modified version of
    Title:      HOL/trancl.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

*)

open Trancl;

(** Natural deduction for trans(r) **)

val prems = goalw Trancl.thy [trans_def]
    "(!! x y z. [| <x,y>:r;  <y,z>:r |] ==> <x,z>:r) ==> trans(r)";
by (REPEAT (ares_tac (prems@[allI,impI]) 1));
qed "transI";

val major::prems = goalw Trancl.thy [trans_def]
    "[| trans(r);  <a,b>:r;  <b,c>:r |] ==> <a,c>:r";
by (cut_facts_tac [major] 1);
by (fast_tac (FOL_cs addIs prems) 1);
qed "transD";

(** Identity relation **)

goalw Trancl.thy [id_def] "<a,a> : id";  
by (rtac CollectI 1);
by (rtac exI 1);
by (rtac refl 1);
qed "idI";

val major::prems = goalw Trancl.thy [id_def]
    "[| p: id;  !!x.[| p = <x,x> |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "idE";

(** Composition of two relations **)

val prems = goalw Trancl.thy [comp_def]
    "[| <a,b>:s; <b,c>:r |] ==> <a,c> : r O s";
by (fast_tac (set_cs addIs prems) 1);
qed "compI";

(*proof requires higher-level assumptions or a delaying of hyp_subst_tac*)
val prems = goalw Trancl.thy [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz = <x,z>;  <x,y>:s;  <y,z>:r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, exE, conjE] 1 ORELSE ares_tac prems 1));
qed "compE";

val prems = goal Trancl.thy
    "[| <a,c> : r O s;  \
\       !!y. [| <a,y>:s;  <y,c>:r |] ==> P \
\    |] ==> P";
by (rtac compE 1);
by (REPEAT (ares_tac prems 1 ORELSE eresolve_tac [pair_inject,ssubst] 1));
qed "compEpair";

val comp_cs = set_cs addIs [compI,idI] 
                       addEs [compE,idE] 
                       addSEs [pair_inject];

val prems = goal Trancl.thy
    "[| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (cut_facts_tac prems 1);
by (fast_tac comp_cs 1);
qed "comp_mono";

(** The relation rtrancl **)

goal Trancl.thy "mono(%s. id Un (r O s))";
by (rtac monoI 1);
by (REPEAT (ares_tac [monoI, subset_refl, comp_mono, Un_mono] 1));
qed "rtrancl_fun_mono";

val rtrancl_unfold = rtrancl_fun_mono RS (rtrancl_def RS def_lfp_Tarski);

(*Reflexivity of rtrancl*)
goal Trancl.thy "<a,a> : r^*";
by (stac rtrancl_unfold 1);
by (fast_tac comp_cs 1);
qed "rtrancl_refl";

(*Closure under composition with r*)
val prems = goal Trancl.thy
    "[| <a,b> : r^*;  <b,c> : r |] ==> <a,c> : r^*";
by (stac rtrancl_unfold 1);
by (fast_tac (comp_cs addIs prems) 1);
qed "rtrancl_into_rtrancl";

(*rtrancl of r contains r*)
val [prem] = goal Trancl.thy "[| <a,b> : r |] ==> <a,b> : r^*";
by (rtac (rtrancl_refl RS rtrancl_into_rtrancl) 1);
by (rtac prem 1);
qed "r_into_rtrancl";


(** standard induction rule **)

val major::prems = goal Trancl.thy 
  "[| <a,b> : r^*; \
\     !!x. P(<x,x>); \
\     !!x y z.[| P(<x,y>); <x,y>: r^*; <y,z>: r |]  ==>  P(<x,z>) |] \
\  ==>  P(<a,b>)";
by (rtac (major RS (rtrancl_def RS def_induct)) 1);
by (rtac rtrancl_fun_mono 1);
by (fast_tac (comp_cs addIs prems) 1);
qed "rtrancl_full_induct";

(*nice induction rule*)
val major::prems = goal Trancl.thy
    "[| <a,b> : r^*;    \
\       P(a); \
\       !!y z.[| <a,y> : r^*;  <y,z> : r;  P(y) |] ==> P(z) |]  \
\     ==> P(b)";
(*by induction on this formula*)
by (subgoal_tac "ALL y. <a,b> = <a,y> --> P(y)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (fast_tac FOL_cs 1);
(*now do the induction*)
by (resolve_tac [major RS rtrancl_full_induct] 1);
by (fast_tac (comp_cs addIs prems) 1);
by (fast_tac (comp_cs addIs prems) 1);
qed "rtrancl_induct";

(*transitivity of transitive closure!! -- by induction.*)
goal Trancl.thy "trans(r^*)";
by (rtac transI 1);
by (res_inst_tac [("b","z")] rtrancl_induct 1);
by (DEPTH_SOLVE (eresolve_tac [asm_rl, rtrancl_into_rtrancl] 1));
qed "trans_rtrancl";

(*elimination of rtrancl -- by induction on a special formula*)
val major::prems = goal Trancl.thy
    "[| <a,b> : r^*;  (a = b) ==> P; \
\       !!y.[| <a,y> : r^*; <y,b> : r |] ==> P |] \
\    ==> P";
by (subgoal_tac "a = b  | (EX y. <a,y> : r^* & <y,b> : r)" 1);
by (rtac (major RS rtrancl_induct) 2);
by (fast_tac (set_cs addIs prems) 2);
by (fast_tac (set_cs addIs prems) 2);
by (REPEAT (eresolve_tac ([asm_rl,exE,disjE,conjE]@prems) 1));
qed "rtranclE";


(**** The relation trancl ****)

(** Conversions between trancl and rtrancl **)

val [major] = goalw Trancl.thy [trancl_def]
    "[| <a,b> : r^+ |] ==> <a,b> : r^*";
by (resolve_tac [major RS compEpair] 1);
by (REPEAT (ares_tac [rtrancl_into_rtrancl] 1));
qed "trancl_into_rtrancl";

(*r^+ contains r*)
val [prem] = goalw Trancl.thy [trancl_def]
   "[| <a,b> : r |] ==> <a,b> : r^+";
by (REPEAT (ares_tac [prem,compI,rtrancl_refl] 1));
qed "r_into_trancl";

(*intro rule by definition: from rtrancl and r*)
val prems = goalw Trancl.thy [trancl_def]
    "[| <a,b> : r^*;  <b,c> : r |]   ==>  <a,c> : r^+";
by (REPEAT (resolve_tac ([compI]@prems) 1));
qed "rtrancl_into_trancl1";

(*intro rule from r and rtrancl*)
val prems = goal Trancl.thy
    "[| <a,b> : r;  <b,c> : r^* |]   ==>  <a,c> : r^+";
by (resolve_tac (prems RL [rtranclE]) 1);
by (etac subst 1);
by (resolve_tac (prems RL [r_into_trancl]) 1);
by (rtac (trans_rtrancl RS transD RS rtrancl_into_trancl1) 1);
by (REPEAT (ares_tac (prems@[r_into_rtrancl]) 1));
qed "rtrancl_into_trancl2";

(*elimination of r^+ -- NOT an induction rule*)
val major::prems = goal Trancl.thy
    "[| <a,b> : r^+;  \
\       <a,b> : r ==> P; \
\       !!y.[| <a,y> : r^+;  <y,b> : r |] ==> P  \
\    |] ==> P";
by (subgoal_tac "<a,b> : r | (EX y. <a,y> : r^+  &  <y,b> : r)" 1);
by (REPEAT (eresolve_tac ([asm_rl,disjE,exE,conjE]@prems) 1));
by (rtac (rewrite_rule [trancl_def] major RS compEpair) 1);
by (etac rtranclE 1);
by (fast_tac comp_cs 1);
by (fast_tac (comp_cs addSIs [rtrancl_into_trancl1]) 1);
qed "tranclE";

(*Transitivity of r^+.
  Proved by unfolding since it uses transitivity of rtrancl. *)
goalw Trancl.thy [trancl_def] "trans(r^+)";
by (rtac transI 1);
by (REPEAT (etac compEpair 1));
by (rtac (rtrancl_into_rtrancl RS (trans_rtrancl RS transD RS compI)) 1);
by (REPEAT (assume_tac 1));
qed "trans_trancl";

val prems = goal Trancl.thy
    "[| <a,b> : r;  <b,c> : r^+ |]   ==>  <a,c> : r^+";
by (rtac (r_into_trancl RS (trans_trancl RS transD)) 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
qed "trancl_into_trancl2";
