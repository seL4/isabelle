(*  Title:      HOL/Trancl
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For Trancl.thy.  Theorems about the transitive closure of a relation
*)

open Trancl;

(** The relation rtrancl **)

goal Trancl.thy "mono(%s. id Un (r O s))";
by (rtac monoI 1);
by (REPEAT (ares_tac [monoI, subset_refl, comp_mono, Un_mono] 1));
qed "rtrancl_fun_mono";

val rtrancl_unfold = rtrancl_fun_mono RS (rtrancl_def RS def_lfp_Tarski);

(*Reflexivity of rtrancl*)
goal Trancl.thy "(a,a) : r^*";
by (stac rtrancl_unfold 1);
by (Blast_tac 1);
qed "rtrancl_refl";

Addsimps [rtrancl_refl];
AddSIs   [rtrancl_refl];


(*Closure under composition with r*)
goal Trancl.thy "!!r. [| (a,b) : r^*;  (b,c) : r |] ==> (a,c) : r^*";
by (stac rtrancl_unfold 1);
by (Blast_tac 1);
qed "rtrancl_into_rtrancl";

(*rtrancl of r contains r*)
goal Trancl.thy "!!p. p : r ==> p : r^*";
by (split_all_tac 1);
by (etac (rtrancl_refl RS rtrancl_into_rtrancl) 1);
qed "r_into_rtrancl";

(*monotonicity of rtrancl*)
goalw Trancl.thy [rtrancl_def] "!!r s. r <= s ==> r^* <= s^*";
by (REPEAT(ares_tac [lfp_mono,Un_mono,comp_mono,subset_refl] 1));
qed "rtrancl_mono";

(** standard induction rule **)

val major::prems = goal Trancl.thy 
  "[| (a,b) : r^*; \
\     !!x. P((x,x)); \
\     !!x y z.[| P((x,y)); (x,y): r^*; (y,z): r |]  ==>  P((x,z)) |] \
\  ==>  P((a,b))";
by (rtac ([rtrancl_def, rtrancl_fun_mono, major] MRS def_induct) 1);
by (blast_tac (claset() addIs prems) 1);
qed "rtrancl_full_induct";

(*nice induction rule*)
val major::prems = goal Trancl.thy
    "[| (a::'a,b) : r^*;    \
\       P(a); \
\       !!y z.[| (a,y) : r^*;  (y,z) : r;  P(y) |] ==> P(z) |]  \
\     ==> P(b)";
(*by induction on this formula*)
by (subgoal_tac "! y. (a::'a,b) = (a,y) --> P(y)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (Blast_tac 1);
(*now do the induction*)
by (resolve_tac [major RS rtrancl_full_induct] 1);
by (blast_tac (claset() addIs prems) 1);
by (blast_tac (claset() addIs prems) 1);
qed "rtrancl_induct";

bind_thm
  ("rtrancl_induct2",
   Prod_Syntax.split_rule
     (read_instantiate [("a","(ax,ay)"), ("b","(bx,by)")] rtrancl_induct));

(*transitivity of transitive closure!! -- by induction.*)
goalw Trancl.thy [trans_def] "trans(r^*)";
by Safe_tac;
by (eres_inst_tac [("b","z")] rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_into_rtrancl])));
qed "trans_rtrancl";

bind_thm ("rtrancl_trans", trans_rtrancl RS transD);


(*elimination of rtrancl -- by induction on a special formula*)
val major::prems = goal Trancl.thy
    "[| (a::'a,b) : r^*;  (a = b) ==> P;        \
\       !!y.[| (a,y) : r^*; (y,b) : r |] ==> P  \
\    |] ==> P";
by (subgoal_tac "(a::'a) = b  | (? y. (a,y) : r^* & (y,b) : r)" 1);
by (rtac (major RS rtrancl_induct) 2);
by (blast_tac (claset() addIs prems) 2);
by (blast_tac (claset() addIs prems) 2);
by (REPEAT (eresolve_tac ([asm_rl,exE,disjE,conjE]@prems) 1));
qed "rtranclE";

bind_thm ("rtrancl_into_rtrancl2", r_into_rtrancl RS rtrancl_trans);


(*** More r^* equations and inclusions ***)

goal Trancl.thy "(r^*)^* = r^*";
by (rtac set_ext 1);
by (res_inst_tac [("p","x")] PairE 1);
by (hyp_subst_tac 1);
by (rtac iffI 1);
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (blast_tac (claset() addIs [rtrancl_trans]) 1);
by (etac r_into_rtrancl 1);
qed "rtrancl_idemp";
Addsimps [rtrancl_idemp];

goal thy "R^* O R^* = R^*";
br set_ext 1;
by(split_all_tac 1);
by(blast_tac (claset() addIs [rtrancl_trans]) 1);
qed "rtrancl_idemp_self_comp";
Addsimps [rtrancl_idemp_self_comp];

goal Trancl.thy "!!r s. r <= s^* ==> r^* <= s^*";
by (dtac rtrancl_mono 1);
by (Asm_full_simp_tac 1);
qed "rtrancl_subset_rtrancl";

goal Trancl.thy "!!R. [| R <= S; S <= R^* |] ==> S^* = R^*";
by (dtac rtrancl_mono 1);
by (dtac rtrancl_mono 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "rtrancl_subset";

goal Trancl.thy "!!R. (R^* Un S^*)^* = (R Un S)^*";
by (blast_tac (claset() addSIs [rtrancl_subset]
                       addIs [r_into_rtrancl, rtrancl_mono RS subsetD]) 1);
qed "rtrancl_Un_rtrancl";

goal Trancl.thy "(R^=)^* = R^*";
by (blast_tac (claset() addSIs [rtrancl_subset]
                       addIs  [rtrancl_refl, r_into_rtrancl]) 1);
qed "rtrancl_reflcl";
Addsimps [rtrancl_reflcl];

goal Trancl.thy "!!r. (x,y) : (r^-1)^* ==> (x,y) : (r^*)^-1";
by (rtac converseI 1);
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "rtrancl_converseD";

goal Trancl.thy "!!r. (x,y) : (r^*)^-1 ==> (x,y) : (r^-1)^*";
by (dtac converseD 1);
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "rtrancl_converseI";

goal Trancl.thy "(r^-1)^* = (r^*)^-1";
by (safe_tac (claset() addSDs [rtrancl_converseD] addSIs [rtrancl_converseI]
			addSaltern ("split_all_tac", split_all_tac)));
qed "rtrancl_converse";

val major::prems = goal Trancl.thy
    "[| (a,b) : r^*; P(b); \
\       !!y z.[| (y,z) : r;  (z,b) : r^*;  P(z) |] ==> P(y) |]  \
\     ==> P(a)";
by (rtac ((major RS converseI RS rtrancl_converseI) RS rtrancl_induct) 1);
by (resolve_tac prems 1);
by (blast_tac (claset() addIs prems addSDs[rtrancl_converseD])1);
qed "converse_rtrancl_induct";

val prems = goal Trancl.thy
 "[| ((a,b),(c,d)) : r^*; P c d; \
\    !!x y z u.[| ((x,y),(z,u)) : r;  ((z,u),(c,d)) : r^*;  P z u |] ==> P x y\
\ |] ==> P a b";
by (res_inst_tac[("R","P")]splitD 1);
by (res_inst_tac[("P","split P")]converse_rtrancl_induct 1);
by (resolve_tac prems 1);
by (Simp_tac 1);
by (resolve_tac prems 1);
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
by (REPEAT(ares_tac prems 1));
qed "converse_rtrancl_induct2";

val major::prems = goal Trancl.thy
 "[| (x,z):r^*; \
\    x=z ==> P; \
\    !!y. [| (x,y):r; (y,z):r^* |] ==> P \
\ |] ==> P";
by (subgoal_tac "x = z  | (? y. (x,y) : r & (y,z) : r^*)" 1);
by (rtac (major RS converse_rtrancl_induct) 2);
by (blast_tac (claset() addIs prems) 2);
by (blast_tac (claset() addIs prems) 2);
by (REPEAT (eresolve_tac ([asm_rl,exE,disjE,conjE]@prems) 1));
qed "rtranclE2";

goal Trancl.thy "r O r^* = r^* O r";
by (blast_tac (claset() addEs [rtranclE, rtranclE2] 
	               addIs [rtrancl_into_rtrancl, rtrancl_into_rtrancl2]) 1);
qed "r_comp_rtrancl_eq";


(**** The relation trancl ****)

goalw Trancl.thy [trancl_def] "!!p.[| p:r^+; r <= s |] ==> p:s^+";
by (blast_tac (claset() addIs [rtrancl_mono RS subsetD]) 1);
qed "trancl_mono";

(** Conversions between trancl and rtrancl **)

goalw Trancl.thy [trancl_def]
    "!!p. p : r^+ ==> p : r^*";
by (split_all_tac 1);
by (etac compEpair 1);
by (REPEAT (ares_tac [rtrancl_into_rtrancl] 1));
qed "trancl_into_rtrancl";

(*r^+ contains r*)
goalw Trancl.thy [trancl_def]
   "!!p. p : r ==> p : r^+";
by (split_all_tac 1);
by (REPEAT (ares_tac [prem,compI,rtrancl_refl] 1));
qed "r_into_trancl";

(*intro rule by definition: from rtrancl and r*)
val prems = goalw Trancl.thy [trancl_def]
    "[| (a,b) : r^*;  (b,c) : r |]   ==>  (a,c) : r^+";
by (REPEAT (resolve_tac ([compI]@prems) 1));
qed "rtrancl_into_trancl1";

(*intro rule from r and rtrancl*)
val prems = goal Trancl.thy
    "[| (a,b) : r;  (b,c) : r^* |]   ==>  (a,c) : r^+";
by (resolve_tac (prems RL [rtranclE]) 1);
by (etac subst 1);
by (resolve_tac (prems RL [r_into_trancl]) 1);
by (rtac (rtrancl_trans RS rtrancl_into_trancl1) 1);
by (REPEAT (ares_tac (prems@[r_into_rtrancl]) 1));
qed "rtrancl_into_trancl2";

(*Nice induction rule for trancl*)
val major::prems = goal Trancl.thy
  "[| (a,b) : r^+;                                      \
\     !!y.  [| (a,y) : r |] ==> P(y);                   \
\     !!y z.[| (a,y) : r^+;  (y,z) : r;  P(y) |] ==> P(z)       \
\  |] ==> P(b)";
by (rtac (rewrite_rule [trancl_def] major  RS  compEpair) 1);
(*by induction on this formula*)
by (subgoal_tac "ALL z. (y,z) : r --> P(z)" 1);
(*now solve first subgoal: this formula is sufficient*)
by (Blast_tac 1);
by (etac rtrancl_induct 1);
by (ALLGOALS (blast_tac (claset() addIs (rtrancl_into_trancl1::prems))));
qed "trancl_induct";

(*elimination of r^+ -- NOT an induction rule*)
val major::prems = goal Trancl.thy
    "[| (a::'a,b) : r^+;  \
\       (a,b) : r ==> P; \
\       !!y.[| (a,y) : r^+;  (y,b) : r |] ==> P  \
\    |] ==> P";
by (subgoal_tac "(a::'a,b) : r | (? y. (a,y) : r^+  &  (y,b) : r)" 1);
by (REPEAT (eresolve_tac ([asm_rl,disjE,exE,conjE]@prems) 1));
by (rtac (rewrite_rule [trancl_def] major RS compEpair) 1);
by (etac rtranclE 1);
by (Blast_tac 1);
by (blast_tac (claset() addSIs [rtrancl_into_trancl1]) 1);
qed "tranclE";

(*Transitivity of r^+.
  Proved by unfolding since it uses transitivity of rtrancl. *)
goalw Trancl.thy [trancl_def] "trans(r^+)";
by (rtac transI 1);
by (REPEAT (etac compEpair 1));
by (rtac (rtrancl_into_rtrancl RS (rtrancl_trans RS compI)) 1);
by (REPEAT (assume_tac 1));
qed "trans_trancl";

bind_thm ("trancl_trans", trans_trancl RS transD);

goalw Trancl.thy [trancl_def]
  "!!r. [| (x,y):r^*; (y,z):r^+ |] ==> (x,z):r^+";
by (blast_tac (claset() addIs [rtrancl_trans,r_into_rtrancl]) 1);
qed "rtrancl_trancl_trancl";

val prems = goal Trancl.thy
    "[| (a,b) : r;  (b,c) : r^+ |]   ==>  (a,c) : r^+";
by (rtac (r_into_trancl RS (trans_trancl RS transD)) 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
qed "trancl_into_trancl2";

(* primitive recursion for trancl over finite relations: *)
goal Trancl.thy "(insert (y,x) r)^+ = r^+ Un {(a,b). (a,y):r^* & (x,b):r^*}";
by (rtac equalityI 1);
 by (rtac subsetI 1);
 by (split_all_tac 1);
 by (etac trancl_induct 1);
  by (blast_tac (claset() addIs [r_into_trancl]) 1);
 by (blast_tac (claset() addIs
     [rtrancl_into_trancl1,trancl_into_rtrancl,r_into_trancl,trancl_trans]) 1);
by (rtac subsetI 1);
by (blast_tac (claset() addIs
     [rtrancl_into_trancl2, rtrancl_trancl_trancl,
      impOfSubs rtrancl_mono, trancl_mono]) 1);
qed "trancl_insert";

goalw Trancl.thy [trancl_def] "(r^-1)^+ = (r^+)^-1";
by (simp_tac (simpset() addsimps [rtrancl_converse,converse_comp]) 1);
by (simp_tac (simpset() addsimps [rtrancl_converse RS sym,r_comp_rtrancl_eq])1);
qed "trancl_converse";

val irrefl_tranclI = prove_goal Trancl.thy 
	"!!r. r^-1 Int r^+ = {} ==> !x. (x, x) ~: r^+" (K [
	rtac allI 1,
	subgoal_tac "!y. (x, y) : r^+ --> x~=y" 1,
	 Fast_tac 1,
	strip_tac 1,
	etac trancl_induct 1,
	 auto_tac (claset() addEs [equals0D, r_into_trancl], simpset())]);

val major::prems = goal Trancl.thy
    "[| (a,b) : r^*;  r <= A Times A |] ==> a=b | a:A";
by (cut_facts_tac prems 1);
by (rtac (major RS rtrancl_induct) 1);
by (rtac (refl RS disjI1) 1);
by (Blast_tac 1);
val lemma = result();

goalw Trancl.thy [trancl_def]
    "!!r. r <= A Times A ==> r^+ <= A Times A";
by (blast_tac (claset() addSDs [lemma]) 1);
qed "trancl_subset_Sigma";


goal Trancl.thy "(r^+)^= = r^*";
by (safe_tac (claset() addSaltern ("split_all_tac", split_all_tac)));
by  (etac trancl_into_rtrancl 1);
by (etac rtranclE 1);
by  (Auto_tac );
by (etac rtrancl_into_trancl1 1);
ba 1;
qed "reflcl_trancl";
Addsimps[reflcl_trancl];

goal Trancl.thy "(r^=)^+ = r^*";
by (safe_tac (claset() addSaltern ("split_all_tac", split_all_tac)));
by  (dtac trancl_into_rtrancl 1);
by  (Asm_full_simp_tac 1);
by (etac rtranclE 1);
by  Safe_tac;
by  (rtac r_into_trancl 1);
by  (Simp_tac 1);
by (rtac rtrancl_into_trancl1 1);
by (etac (rtrancl_reflcl RS equalityD2 RS subsetD) 1);
by (Fast_tac 1);
qed "trancl_reflcl";
Addsimps[trancl_reflcl];

qed_goal "trancl_empty" Trancl.thy "{}^+ = {}" 
  (K [auto_tac (claset() addEs [trancl_induct], simpset())]);
Addsimps[trancl_empty];

qed_goal "rtrancl_empty" Trancl.thy "{}^* = id" 
  (K [rtac (reflcl_trancl RS subst) 1, Simp_tac 1]);
Addsimps[rtrancl_empty];
