(*  Title:      HOL/Trancl
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Theorems about the transitive closure of a relation
*)

(** The relation rtrancl **)

section "^*";

Goal "mono(%s. Id Un (r O s))";
by (rtac monoI 1);
by (REPEAT (ares_tac [monoI, subset_refl, comp_mono, Un_mono] 1));
qed "rtrancl_fun_mono";

val rtrancl_unfold = rtrancl_fun_mono RS (rtrancl_def RS def_lfp_Tarski);

(*Reflexivity of rtrancl*)
Goal "(a,a) : r^*";
by (stac rtrancl_unfold 1);
by (Blast_tac 1);
qed "rtrancl_refl";

Addsimps [rtrancl_refl];
AddSIs   [rtrancl_refl];


(*Closure under composition with r*)
Goal "[| (a,b) : r^*;  (b,c) : r |] ==> (a,c) : r^*";
by (stac rtrancl_unfold 1);
by (Blast_tac 1);
qed "rtrancl_into_rtrancl";

(*rtrancl of r contains r*)
Goal "!!p. p : r ==> p : r^*";
by (split_all_tac 1);
by (etac (rtrancl_refl RS rtrancl_into_rtrancl) 1);
qed "r_into_rtrancl";

(*monotonicity of rtrancl*)
Goalw [rtrancl_def] "r <= s ==> r^* <= s^*";
by (REPEAT(ares_tac [lfp_mono,Un_mono,comp_mono,subset_refl] 1));
qed "rtrancl_mono";

(** standard induction rule **)

val major::prems = Goal 
  "[| (a,b) : r^*; \
\     !!x. P((x,x)); \
\     !!x y z.[| P((x,y)); (x,y): r^*; (y,z): r |]  ==>  P((x,z)) |] \
\  ==>  P((a,b))";
by (rtac ([rtrancl_def, rtrancl_fun_mono, major] MRS def_induct) 1);
by (blast_tac (claset() addIs prems) 1);
qed "rtrancl_full_induct";

(*nice induction rule*)
val major::prems = Goal
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

bind_thm ("rtrancl_induct2", split_rule
  (read_instantiate [("a","(ax,ay)"), ("b","(bx,by)")] rtrancl_induct));

(*transitivity of transitive closure!! -- by induction.*)
Goalw [trans_def] "trans(r^*)";
by Safe_tac;
by (eres_inst_tac [("b","z")] rtrancl_induct 1);
by (ALLGOALS(blast_tac (claset() addIs [rtrancl_into_rtrancl])));
qed "trans_rtrancl";

bind_thm ("rtrancl_trans", trans_rtrancl RS transD);


(*elimination of rtrancl -- by induction on a special formula*)
val major::prems = Goal
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

Goal "(r^*)^* = r^*";
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

Goal "R^* O R^* = R^*";
by (rtac set_ext 1);
by (split_all_tac 1);
by (blast_tac (claset() addIs [rtrancl_trans]) 1);
qed "rtrancl_idemp_self_comp";
Addsimps [rtrancl_idemp_self_comp];

Goal "r <= s^* ==> r^* <= s^*";
by (dtac rtrancl_mono 1);
by (Asm_full_simp_tac 1);
qed "rtrancl_subset_rtrancl";

Goal "[| R <= S; S <= R^* |] ==> S^* = R^*";
by (dtac rtrancl_mono 1);
by (dtac rtrancl_mono 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "rtrancl_subset";

Goal "(R^* Un S^*)^* = (R Un S)^*";
by (blast_tac (claset() addSIs [rtrancl_subset]
                        addIs [r_into_rtrancl, rtrancl_mono RS subsetD]) 1);
qed "rtrancl_Un_rtrancl";

Goal "(R^=)^* = R^*";
by (blast_tac (claset() addSIs [rtrancl_subset] addIs [r_into_rtrancl]) 1);
qed "rtrancl_reflcl";
Addsimps [rtrancl_reflcl];

Goal "(x,y) : (r^-1)^* ==> (x,y) : (r^*)^-1";
by (rtac converseI 1);
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "rtrancl_converseD";

Goal "(x,y) : (r^*)^-1 ==> (x,y) : (r^-1)^*";
by (dtac converseD 1);
by (etac rtrancl_induct 1);
by (rtac rtrancl_refl 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "rtrancl_converseI";

Goal "(r^-1)^* = (r^*)^-1";
by (safe_tac (claset() addSDs [rtrancl_converseD] addSIs [rtrancl_converseI]));
qed "rtrancl_converse";

val major::prems = Goal
    "[| (a,b) : r^*; P(b); \
\       !!y z.[| (y,z) : r;  (z,b) : r^*;  P(z) |] ==> P(y) |]  \
\     ==> P(a)";
by (rtac ((major RS converseI RS rtrancl_converseI) RS rtrancl_induct) 1);
by (resolve_tac prems 1);
by (blast_tac (claset() addIs prems addSDs[rtrancl_converseD])1);
qed "converse_rtrancl_induct";

bind_thm ("converse_rtrancl_induct2", split_rule
  (read_instantiate [("a","(ax,ay)"),("b","(bx,by)")]converse_rtrancl_induct));

val major::prems = Goal
 "[| (x,z):r^*; \
\    x=z ==> P; \
\    !!y. [| (x,y):r; (y,z):r^* |] ==> P \
\ |] ==> P";
by (subgoal_tac "x = z  | (? y. (x,y) : r & (y,z) : r^*)" 1);
by (rtac (major RS converse_rtrancl_induct) 2);
by (blast_tac (claset() addIs prems) 2);
by (blast_tac (claset() addIs prems) 2);
by (REPEAT (eresolve_tac ([asm_rl,exE,disjE,conjE]@prems) 1));
qed "converse_rtranclE";

bind_thm ("converse_rtranclE2", split_rule
  (read_instantiate [("x","(xa,xb)"), ("z","(za,zb)")] converse_rtranclE));

Goal "r O r^* = r^* O r";
by (blast_tac (claset() addEs [rtranclE, converse_rtranclE] 
	               addIs [rtrancl_into_rtrancl, rtrancl_into_rtrancl2]) 1);
qed "r_comp_rtrancl_eq";


(**** The relation trancl ****)

section "^+";

Goalw [trancl_def] "[| p:r^+; r <= s |] ==> p:s^+";
by (blast_tac (claset() addIs [rtrancl_mono RS subsetD]) 1);
qed "trancl_mono";

(** Conversions between trancl and rtrancl **)

Goalw [trancl_def]
    "!!p. p : r^+ ==> p : r^*";
by (split_all_tac 1);
by (etac compEpair 1);
by (REPEAT (ares_tac [rtrancl_into_rtrancl] 1));
qed "trancl_into_rtrancl";

(*r^+ contains r*)
Goalw [trancl_def]
   "!!p. p : r ==> p : r^+";
by (split_all_tac 1);
by (REPEAT (ares_tac [prem,compI,rtrancl_refl] 1));
qed "r_into_trancl";

(*intro rule by definition: from rtrancl and r*)
Goalw [trancl_def] "[| (a,b) : r^*;  (b,c) : r |]   ==>  (a,c) : r^+";
by Auto_tac;
qed "rtrancl_into_trancl1";

(*intro rule from r and rtrancl*)
Goal "[| (a,b) : r;  (b,c) : r^* |]   ==>  (a,c) : r^+";
by (etac rtranclE 1);
by (blast_tac (claset() addIs [r_into_trancl]) 1);
by (rtac (rtrancl_trans RS rtrancl_into_trancl1) 1);
by (REPEAT (ares_tac [r_into_rtrancl] 1));
qed "rtrancl_into_trancl2";

(*Nice induction rule for trancl*)
val major::prems = Goal
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

(*Another induction rule for trancl, incorporating transitivity.*)
val major::prems = goal thy
 "[| (x,y) : r^+; \
\    !!x y. (x,y) : r ==> P x y; \
\    !!x y z. [| (x,y) : r^+; P x y; (y,z) : r^+; P y z |] ==> P x z \
\ |] ==> P x y";
by(blast_tac (claset() addIs ([r_into_trancl,major RS trancl_induct]@prems))1);
qed "trancl_trans_induct";

(*elimination of r^+ -- NOT an induction rule*)
val major::prems = Goal
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
Goalw [trancl_def] "trans(r^+)";
by (rtac transI 1);
by (REPEAT (etac compEpair 1));
by (rtac (rtrancl_into_rtrancl RS (rtrancl_trans RS compI)) 1);
by (REPEAT (assume_tac 1));
qed "trans_trancl";

bind_thm ("trancl_trans", trans_trancl RS transD);

Goalw [trancl_def] "[| (x,y):r^*; (y,z):r^+ |] ==> (x,z):r^+";
by (blast_tac (claset() addIs [rtrancl_trans,r_into_rtrancl]) 1);
qed "rtrancl_trancl_trancl";

(* "[| (a,b) : r;  (b,c) : r^+ |]   ==>  (a,c) : r^+" *)
bind_thm ("trancl_into_trancl2", [trans_trancl, r_into_trancl] MRS transD);

(* primitive recursion for trancl over finite relations: *)
Goal "(insert (y,x) r)^+ = r^+ Un {(a,b). (a,y):r^* & (x,b):r^*}";
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

Goalw [trancl_def] "(r^-1)^+ = (r^+)^-1";
by (simp_tac (simpset() addsimps [rtrancl_converse,converse_comp]) 1);
by (simp_tac (simpset() addsimps [rtrancl_converse RS sym,
				  r_comp_rtrancl_eq]) 1);
qed "trancl_converse";

Goal "(x,y) : (r^+)^-1 ==> (x,y) : (r^-1)^+";
by (asm_full_simp_tac (simpset() addsimps [trancl_converse]) 1);
qed "trancl_converseI";

Goal "(x,y) : (r^-1)^+ ==> (x,y) : (r^+)^-1";
by (asm_full_simp_tac (simpset() addsimps [trancl_converse]) 1);
qed "trancl_converseD";

val major::prems = Goal
    "[| (a,b) : r^+; !!y. (y,b) : r ==> P(y); \
\       !!y z.[| (y,z) : r;  (z,b) : r^+;  P(z) |] ==> P(y) |]  \
\     ==> P(a)";
by (rtac ((major RS converseI RS trancl_converseI) RS trancl_induct) 1);
 by (resolve_tac prems 1);
 by (etac converseD 1);
by (blast_tac (claset() addIs prems addSDs [trancl_converseD])1);
qed "converse_trancl_induct";

(*Unused*)
qed_goal "irrefl_tranclI" Trancl.thy 
   "!!r. r^-1 Int r^+ = {} ==> (x, x) ~: r^+" 
 (K [subgoal_tac "!y. (x, y) : r^+ --> x~=y" 1,
     Fast_tac 1,
     strip_tac 1,
     etac trancl_induct 1,
     auto_tac (claset() addIs [r_into_trancl], simpset())]);

Goal "[| (a,b) : r^*;  r <= A Times A |] ==> a=b | a:A";
by (etac rtrancl_induct 1);
by Auto_tac;
val lemma = result();

Goalw [trancl_def] "r <= A Times A ==> r^+ <= A Times A";
by (blast_tac (claset() addSDs [lemma]) 1);
qed "trancl_subset_Sigma";


Goal "(r^+)^= = r^*";
by Safe_tac;
by  (etac trancl_into_rtrancl 1);
by (etac rtranclE 1);
by  (Auto_tac );
by (etac rtrancl_into_trancl1 1);
by (assume_tac 1);
qed "reflcl_trancl";
Addsimps[reflcl_trancl];

Goal "(r^=)^+ = r^*";
by Safe_tac;
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

qed_goal "rtrancl_empty" Trancl.thy "{}^* = Id" 
  (K [rtac (reflcl_trancl RS subst) 1, Simp_tac 1]);
Addsimps[rtrancl_empty];
