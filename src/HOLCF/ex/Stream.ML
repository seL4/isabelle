(*  Title: 	HOLCF/ex//Stream.ML
    ID:         $Id$
    Author: 	Franz Regensburger, David von Oheimb
    Copyright   1993, 1995 Technische Universitaet Muenchen

general Stream domain
*)

fun stream_case_tac s i = res_inst_tac [("x",s)] stream.casedist i
			  THEN hyp_subst_tac i THEN hyp_subst_tac (i+1);


val [stream_con_rew1,stream_con_rew2] = stream.con_rews;

Addsimps stream.take_rews;
Addsimps stream.when_rews;
Addsimps stream.sel_rews;

(* ----------------------------------------------------------------------- *)
(* theorems about scons                                                    *)
(* ----------------------------------------------------------------------- *)

section "scons";

Goal "a && s = UU = (a = UU)";
by Safe_tac;
by (etac contrapos2 1);
by (safe_tac (claset() addSIs stream.con_rews));
qed "scons_eq_UU";

Goal "[| a && x = UU; a ~= UU |] ==> R";
by (dresolve_tac [stream_con_rew2] 1);
by (contr_tac 1);
qed "scons_not_empty";

Goal "x ~= UU = (EX a y. a ~= UU &  x = a && y)";
by (cut_facts_tac [stream.exhaust] 1);
by (best_tac (claset() addDs [stream_con_rew2]) 1);
qed "stream_exhaust_eq";

Goal 
"[| a && s << t; a ~= UU  |] ==> EX b tt. t = b && tt &  b ~= UU &  s << tt";
by (stream_case_tac "t" 1);
by (fast_tac (claset() addDs [eq_UU_iff RS iffD2, stream_con_rew2]) 1);
by (fast_tac (claset() addDs stream.inverts) 1);
qed "stream_prefix";

Goal "[| x && xs << y && ys; (x::'a::flat) ~= UU|] ==> x = y & xs << ys";
by (cut_inst_tac [("x1","x::'a::flat"), ("x","y::'a::flat")] 
                 (ax_flat RS spec RS spec) 1);
by (forward_tac stream.inverts 1);
by Safe_tac;
by (dtac (hd stream.con_rews RS subst) 1);
by (fast_tac (claset() addDs [eq_UU_iff RS iffD2, stream_con_rew2]) 1);
qed "stream_flat_prefix";

Goal "b ~= UU ==> x << b && z = \
\           (x = UU |  (EX a y. x = a && y &  a ~= UU &  a << b &  y << z))";
by Safe_tac;
by (stream_case_tac "x" 1);
by (safe_tac (claset() addSDs stream.inverts 
                addSIs [minimal, monofun_cfun, monofun_cfun_arg]));
by (Fast_tac 1);
qed "stream_prefix'";

Goal "[| a ~= UU; b ~= UU |] ==> (a && s = b && t) = (a = b &  s = t)";
by (best_tac (claset() addSEs stream.injects) 1);
qed "stream_inject_eq";	


(* ----------------------------------------------------------------------- *)
(* theorems about stream_when                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_when";

Goal "stream_when`UU`s=UU";
by (stream_case_tac "s" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [strict_Rep_CFun1])));
qed "stream_when_strictf";
	

(* ----------------------------------------------------------------------- *)
(* theorems about ft and rt                                                *)
(* ----------------------------------------------------------------------- *)

section "ft & rt";

(*
Goal "ft`s=UU --> s=UU";
by (stream_case_tac "s" 1);
by (REPEAT (asm_simp_tac (simpset() addsimps stream.rews) 1));
qed "stream_ft_lemma1";
*)

Goal "s~=UU ==> ft`s~=UU";
by (stream_case_tac "s" 1);
by (Blast_tac 1);
by (asm_simp_tac (simpset() addsimps stream.rews) 1);
qed "ft_defin";

Goal "rt`s~=UU ==> s~=UU";
by Auto_tac;
qed "rt_strict_rev";

Goal "(ft`s)&&(rt`s)=s";
by (stream_case_tac "s" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps stream.rews)));
qed "surjectiv_scons";

Goal "ALL x s. x << s --> iterate i rt x << iterate i rt s";
by (induct_tac "i" 1);
by (Simp_tac 1);
by (strip_tac 1);
by (stream_case_tac "x" 1);
by (rtac (minimal RS (monofun_iterate2 RS monofunE RS spec RS spec RS mp))1);
by (dtac stream_prefix 1);
by Safe_tac;
by (asm_simp_tac (HOL_ss addsimps iterate_Suc2::stream.rews) 1);
qed_spec_mp "monofun_rt_mult";

			

(* ----------------------------------------------------------------------- *)
(* theorems about stream_take                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_take";

Goal  "(LUB i. stream_take i`s) = s";
by (subgoal_tac "(LUB i. stream_take i`s) = fix`stream_copy`s" 1);
by (simp_tac (simpset() addsimps [fix_def2, stream.take_def,
                                  contlub_cfun_fun, chain_iterate]) 2);
by (asm_full_simp_tac (simpset() addsimps [stream.reach]) 1);
qed "stream_reach2";

Goal "chain (%i. stream_take i`s)";
by (rtac chainI 1);
by (subgoal_tac "ALL i s. stream_take i`s << stream_take (Suc i)`s" 1);
by (Fast_tac 1);
by (rtac allI 1);
by (induct_tac "ia" 1);
by (Simp_tac 1);
by (rtac allI 1);
by (stream_case_tac "s" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [monofun_cfun_arg]) 1);
qed "chain_stream_take";


Goalw [stream.take_def]
	"stream_take n`x = x ==> stream_take (Suc n)`x = x";
by (rtac antisym_less 1);
by (subgoal_tac "iterate (Suc n) stream_copy UU`x << fix`stream_copy`x" 1);
by (asm_full_simp_tac (simpset() addsimps [stream.reach]) 1);
by (rtac monofun_cfun_fun 1);
by (stac fix_def2 1);
by (rtac is_ub_thelub 1);
by (rtac chain_iterate 1);
by (etac subst 1 THEN rtac monofun_cfun_fun 1);
by (rtac (rewrite_rule [chain] chain_iterate RS spec) 1);
qed "stream_take_more";

(*
Goal 
 "ALL  s2. stream_take n`s2 = s2 --> stream_take (Suc n)`s2=s2";
by (induct_tac "n" 1);
by (simp_tac (simpset() addsimps stream_rews) 1);
by (strip_tac 1);
by (hyp_subst_tac  1);
by (simp_tac (simpset() addsimps stream_rews) 1);
by (rtac allI 1);
by (res_inst_tac [("s","s2")] streamE 1);
by (asm_simp_tac (simpset() addsimps stream_rews) 1);
by (asm_simp_tac (simpset() addsimps stream_rews) 1);
by (strip_tac 1 );
by (subgoal_tac "stream_take n1`xs = xs" 1);
by (rtac ((hd stream_inject) RS conjunct2) 2);
by (atac 4);
by (atac 2);
by (atac 2);
by (rtac cfun_arg_cong 1);
by (Blast_tac 1);
qed "stream_take_lemma2";
*)

Goal 
 "ALL x xs. x~=UU --> stream_take n`(x && xs) = x && xs --> stream_take n`xs=xs";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (strip_tac 1);
by (res_inst_tac [("P","x && xs=UU")] notE 1);
by (eresolve_tac stream.con_rews 1);
by (etac sym 1);
by (strip_tac 1);
by (rtac stream_take_more 1);
by (res_inst_tac [("a1","x")] ((hd stream.injects) RS conjunct2) 1);
by (assume_tac 3);
by (etac (hd(tl(tl(stream.take_rews))) RS subst) 1);
by (atac 1);
qed_spec_mp "stream_take_lemma3";

Goal 
 "ALL x xs. stream_take n`xs=xs --> stream_take (Suc n)`(x && xs) = x && xs";
by (induct_tac "n" 1);
by Auto_tac;  
qed_spec_mp "stream_take_lemma4";


(* ------------------------------------------------------------------------- *)
(* special induction rules                                                   *)
(* ------------------------------------------------------------------------- *)

section "induction";


val prems = Goalw [stream.finite_def]
 "[| stream_finite x;  \
\    P UU; \
\    !!a s. [| a ~= UU; P s |] \
\ ==> P (a && s) |] ==> P x";
by (cut_facts_tac prems 1);
by (etac exE 1);
by (etac subst 1);
by (rtac stream.finite_ind 1);
by (atac 1);
by (eresolve_tac prems 1);
by (atac 1);
qed "stream_finite_ind";

val major::prems = Goal
"[| P UU;\
\   !! x    .    x ~= UU                  ==> P (x      && UU); \
\   !! y z s. [| y ~= UU; z ~= UU; P s |] ==> P (y && z && s )  \
\   |] ==> !s. P (stream_take n`s)";
by (res_inst_tac [("n","n")] nat_induct2 1);
by (asm_simp_tac (simpset() addsimps [major]) 1);
by (rtac allI 1);
by (stream_case_tac "s" 1);
by (asm_simp_tac (simpset() addsimps [major]) 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
by (rtac allI 1);
by (stream_case_tac "s" 1);
by (asm_simp_tac (simpset() addsimps [major]) 1);
by (res_inst_tac [("x","sa")] stream.casedist 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "stream_finite_ind2";


val prems = Goal
"[| adm P; P UU; !!a. a ~= UU ==> P (a && UU); \
\   !!a b s. [| a ~= UU; b ~= UU; P s |] ==> P (a && b && s)\
\ |] ==> P x";
by (rtac (stream.reach RS subst) 1);
by (rtac (adm_impl_admw RS wfix_ind) 1);
by (rtac adm_subst 1);
by (cont_tacR 1);
by (resolve_tac prems 1);
by (rtac allI 1);
by (rtac (rewrite_rule [stream.take_def] stream_finite_ind2 RS spec) 1);
by (resolve_tac prems 1);
by (eresolve_tac prems 1);
by (eresolve_tac prems 1);
by (atac 1);
by (atac 1);
qed "stream_ind2";


(* ----------------------------------------------------------------------- *)
(* simplify use of coinduction                                             *)
(* ----------------------------------------------------------------------- *)

section "coinduction";


Goalw [stream.bisim_def]
"!s1 s2. R s1 s2 --> ft`s1 = ft`s2 &  R (rt`s1) (rt`s2) ==> stream_bisim R";
by (strip_tac 1);
by (etac allE 1);
by (etac allE 1);
by (dtac mp 1);
by (atac 1);
by (etac conjE 1);
by (case_tac "x = UU & x' = UU" 1);
by (rtac disjI1 1);
by (Blast_tac 1);
by (rtac disjI2 1);
by (rtac disjE 1);
by (etac (de_Morgan_conj RS subst) 1);
by (res_inst_tac [("x","ft`x")] exI 1);
by (res_inst_tac [("x","rt`x")] exI 1);
by (res_inst_tac [("x","rt`x'")] exI 1);
by (rtac conjI 1);
by (etac ft_defin 1);
by (asm_simp_tac (simpset() addsimps stream.rews addsimps [surjectiv_scons]) 1);
by (eres_inst_tac [("s","ft`x"),("t","ft`x'")] subst 1);
by (simp_tac (simpset() addsimps stream.rews addsimps [surjectiv_scons]) 1);
by (res_inst_tac [("x","ft`x'")] exI 1);
by (res_inst_tac [("x","rt`x")] exI 1);
by (res_inst_tac [("x","rt`x'")] exI 1);
by (rtac conjI 1);
by (etac ft_defin 1);
by (asm_simp_tac (simpset() addsimps stream.rews addsimps [surjectiv_scons]) 1);
by (res_inst_tac [("s","ft`x"),("t","ft`x'")] ssubst 1);
by (etac sym 1);
by (simp_tac (simpset() addsimps stream.rews addsimps [surjectiv_scons]) 1);
qed "stream_coind_lemma2";

(* ----------------------------------------------------------------------- *)
(* theorems about stream_finite                                            *)
(* ----------------------------------------------------------------------- *)

section "stream_finite";


Goalw [stream.finite_def] "stream_finite UU";
by (rtac exI 1);
by (simp_tac (simpset() addsimps stream.rews) 1);
qed "stream_finite_UU";

Goal  "~  stream_finite s ==> s ~= UU";
by (blast_tac (claset() addIs [stream_finite_UU]) 1);
qed "stream_finite_UU_rev";

Goalw [stream.finite_def] "stream_finite xs ==> stream_finite (x && xs)";
by (blast_tac (claset() addIs [stream_take_lemma4]) 1);
qed "stream_finite_lemma1";

Goalw [stream.finite_def]
 "[| x ~= UU; stream_finite (x && xs) |] ==> stream_finite xs";
by (blast_tac (claset() addIs [stream_take_lemma3]) 1);
qed "stream_finite_lemma2";

Goal "stream_finite (rt`s) = stream_finite s";
by (stream_case_tac "s" 1);
by (simp_tac (simpset() addsimps [stream_finite_UU]) 1);
by (Asm_simp_tac 1);
by (fast_tac (claset() addIs [stream_finite_lemma1] 
                       addDs [stream_finite_lemma2]) 1);
qed "stream_finite_rt_eq";

Goal "stream_finite s ==> !t. t<<s --> stream_finite t";
by (eres_inst_tac [("x","s")] stream_finite_ind 1);
by (strip_tac 1); 
by (dtac UU_I 1);
by (asm_simp_tac (simpset() addsimps [stream_finite_UU]) 1);
by (strip_tac 1);
by (asm_full_simp_tac (simpset() addsimps [stream_prefix']) 1);
by (fast_tac (claset() addSIs [stream_finite_UU, stream_finite_lemma1]) 1);
qed_spec_mp "stream_finite_less";

Goal "adm (%x. ~  stream_finite x)";
by (rtac admI2 1);
by (best_tac (claset() addIs [stream_finite_less, is_ub_thelub]) 1);
qed "adm_not_stream_finite";
