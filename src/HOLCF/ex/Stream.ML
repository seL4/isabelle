(*  Title: 	HOLCF/ex//Stream.ML
    ID:         $Id$
    Author: 	Franz Regensburger, David von Oheimb
    Copyright   1993, 1995 Technische Universitaet Muenchen
    Author: 	David von Oheimb (major extensions)
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

general Stream domain
*)

fun stream_case_tac s i = res_inst_tac [("x",s)] stream.casedist i
			  THEN hyp_subst_tac i THEN hyp_subst_tac (i+1);


val [stream_con_rew1,stream_con_rew2] = stream.con_rews;

Addsimps stream.rews;
Addsimps[eq_UU_iff RS sym];

(* ----------------------------------------------------------------------- *)
(* theorems about scons                                                    *)
(* ----------------------------------------------------------------------- *)

section "scons";

Goal "a && s = UU = (a = UU)";
by Safe_tac;
by (etac contrapos_pp 1);
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
                addSIs [monofun_cfun, monofun_cfun_arg]));
by (Fast_tac 1);
qed "stream_prefix'";

Goal "[| a ~= UU; b ~= UU |] ==> (a && s = b && t) = (a = b &  s = t)";
by (best_tac (claset() addSEs stream.injects) 1);
qed "stream_inject_eq";	
Addsimps [stream_inject_eq];


(* ----------------------------------------------------------------------- *)
(* theorems about stream_when                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_when";

Goal "stream_when$UU$s=UU";
by (stream_case_tac "s" 1);
by (ALLGOALS Asm_simp_tac);
qed "stream_when_strictf";
	

(* ----------------------------------------------------------------------- *)
(* theorems about ft and rt                                                *)
(* ----------------------------------------------------------------------- *)

section "ft & rt";

(*
Goal "ft$s=UU --> s=UU";
by (stream_case_tac "s" 1);
by (REPEAT (asm_simp_tac (simpset() addsimps stream.rews) 1));
qed "stream_ft_lemma1";
*)

Goal "s~=UU ==> ft$s~=UU";
by (stream_case_tac "s" 1);
by  (Blast_tac 1);
by (Asm_simp_tac 1);
qed "ft_defin";

Goal "rt$s~=UU ==> s~=UU";
by Auto_tac;
qed "rt_strict_rev";

Goal "(ft$s)&&(rt$s)=s";
by (stream_case_tac "s" 1);
by (ALLGOALS Asm_simp_tac);
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

Goal  "(LUB i. stream_take i$s) = s";
by (subgoal_tac "(LUB i. stream_take i$s) = fix$stream_copy$s" 1);
by (simp_tac (simpset() addsimps [fix_def2, stream.take_def,
                                  contlub_cfun_fun, chain_iterate]) 2);
by (asm_full_simp_tac (simpset() addsimps [stream.reach]) 1);
qed "stream_reach2";

Goal "chain (%i. stream_take i$s)";
by (rtac chainI 1);
by (subgoal_tac "ALL i s::'a stream. stream_take i$s << stream_take (Suc i)$s" 1);
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
	"stream_take n$x = x ==> stream_take (Suc n)$x = x";
by (rtac antisym_less 1);
by (subgoal_tac "iterate (Suc n) stream_copy UU$x << fix$stream_copy$x" 1);
by (asm_full_simp_tac (simpset() addsimps [stream.reach]) 1);
by (rtac monofun_cfun_fun 1);
by (stac fix_def2 1);
by (rtac is_ub_thelub 1);
by (rtac chain_iterate 1);
by (etac subst 1 THEN rtac monofun_cfun_fun 1);
by (rtac (rewrite_rule [chain_def] chain_iterate RS spec) 1);
qed "stream_take_more";

(*
Goal 
 "ALL  s2. stream_take n$s2 = s2 --> stream_take (Suc n)$s2=s2";
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
by (subgoal_tac "stream_take n1$xs = xs" 1);
by (rtac ((hd stream_inject) RS conjunct2) 2);
by (atac 4);
by (atac 2);
by (atac 2);
by (rtac cfun_arg_cong 1);
by (Blast_tac 1);
qed "stream_take_lemma2";
*)

Goal 
"ALL x xs. x~=UU --> stream_take n$(x && xs) = x && xs --> stream_take n$xs=xs";
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
 "ALL x xs. stream_take n$xs=xs --> stream_take (Suc n)$(x && xs) = x && xs";
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
\   |] ==> !s. P (stream_take n$s)";
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
"!s1 s2. R s1 s2 --> ft$s1 = ft$s2 &  R (rt$s1) (rt$s2) ==> stream_bisim R";
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
by (res_inst_tac [("x","ft$x")] exI 1);
by (res_inst_tac [("x","rt$x")] exI 1);
by (res_inst_tac [("x","rt$x'")] exI 1);
by (rtac conjI 1);
by (etac ft_defin 1);
by (asm_simp_tac (simpset() addsimps [surjectiv_scons]) 1);
by (eres_inst_tac [("s","ft$x"),("t","ft$x'")] subst 1);
by (simp_tac (simpset() addsimps [surjectiv_scons]) 1);
by (res_inst_tac [("x","ft$x'")] exI 1);
by (res_inst_tac [("x","rt$x")] exI 1);
by (res_inst_tac [("x","rt$x'")] exI 1);
by (rtac conjI 1);
by (etac ft_defin 1);
by (asm_simp_tac (simpset() addsimps [surjectiv_scons]) 1);
by (res_inst_tac [("s","ft$x"),("t","ft$x'")] ssubst 1);
by (etac sym 1);
by (simp_tac (simpset() addsimps [surjectiv_scons]) 1);
qed "stream_coind_lemma2";

(* ----------------------------------------------------------------------- *)
(* theorems about stream_finite                                            *)
(* ----------------------------------------------------------------------- *)

section "stream_finite";


Goalw [stream.finite_def] "stream_finite UU";
by (rtac exI 1);
by (Simp_tac 1);
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

Goal "stream_finite (rt$s) = stream_finite s";
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

section "smap";

bind_thm ("smap_unfold", fix_prover2 thy smap_def 
	"smap = (\\<Lambda>f s. case s of x && l => f\\<cdot>x && smap\\<cdot>f\\<cdot>l)");

Goal "smap\\<cdot>f\\<cdot>\\<bottom> = \\<bottom>";
by (stac smap_unfold 1);
by (Simp_tac 1);
qed "smap_empty";

Goal "x~=\\<bottom> ==> smap\\<cdot>f\\<cdot>(x&&xs) = (f\\<cdot>x)&&(smap\\<cdot>f\\<cdot>xs)";
by (rtac trans 1);
by  (stac smap_unfold 1);
by  (Asm_simp_tac 1);
by (rtac refl 1);
qed "smap_scons";

Addsimps [smap_empty, smap_scons];

(* ------------------------------------------------------------------------- *)

section "slen";

Goalw [slen_def, stream.finite_def] "#\\<bottom> = 0";
by (Simp_tac 1);
by (stac Least_equality 1);
by    Auto_tac;
by (simp_tac(simpset() addsimps [thm "Fin_0"]) 1);
qed "slen_empty";

Goalw [slen_def] "x ~= \\<bottom> ==> #(x&&xs) = iSuc (#xs)";
by (res_inst_tac [("Q1","stream_finite (x && xs)")] (split_if RS iffD2) 1);
by Safe_tac;
by (rtac (split_if RS iffD2) 2);
by  Safe_tac;
by   (fast_tac (claset() addIs [stream_finite_lemma1]) 2);
by  (rtac (thm "iSuc_Infty" RS sym) 2);
by (rtac (split_if RS iffD2) 1);
by (Simp_tac 1);
by Safe_tac;
by  (eatac stream_finite_lemma2 1 2);
by (rewtac stream.finite_def);
by (Clarify_tac 1);
by (eatac Least_Suc2 1 1);
by  (rtac not_sym 1);
by  Auto_tac;
qed "slen_scons"; 

Addsimps [slen_empty, slen_scons];

Goal "#x < Fin 1' = (x = UU)";
by (stream_case_tac "x" 1);
by (auto_tac (claset(), simpset() delsimps [thm "iSuc_Fin"] addsimps
 [thm "Fin_0", thm "iSuc_Fin" RS sym, thm "i0_iless_iSuc", thm "iSuc_mono"]));
qed "slen_less_1_eq";

Goal "(#x = 0) = (x = \\<bottom>)";
by Auto_tac;
by (stream_case_tac "x" 1);
by (rotate_tac ~1 2);
by Auto_tac;
qed "slen_empty_eq";

Goal "Fin (Suc n) < #x = (? a y. x = a && y &  a ~= \\<bottom> &  Fin n < #y)";
by (stream_case_tac "x" 1);
by (auto_tac (claset(), simpset() delsimps [thm "iSuc_Fin"] addsimps
                [thm "iSuc_Fin" RS sym, thm "iSuc_mono"]));
by  (dtac sym 1);
by  (rotate_tac 2 2);
by  Auto_tac;
qed "slen_scons_eq";


Goal "#x = iSuc n --> (? a y. x = a&&y &  a ~= \\<bottom> &  #y = n)";
by (stream_case_tac "x" 1);
by Auto_tac;
qed_spec_mp "slen_iSuc";


Goal 
"#x < Fin (Suc (Suc n)) = (!a y. x ~= a && y |  a = \\<bottom> |  #y < Fin (Suc n))";
by (stac (thm "iSuc_Fin" RS sym) 1);
by (stac (thm "iSuc_Fin" RS sym) 1);
by (safe_tac HOL_cs);
by  (rotate_tac ~1 1);
by  (asm_full_simp_tac (HOL_ss addsimps [slen_scons, thm "iSuc_mono"]) 1);
by  (Asm_full_simp_tac 1);
by (stream_case_tac "x" 1);
by ( simp_tac (HOL_ss addsimps [slen_empty, thm "i0_iless_iSuc"]) 1);
by (asm_simp_tac (HOL_ss addsimps [slen_scons, thm "iSuc_mono"]) 1);
by (etac allE 1);
by (etac allE 1);
by (safe_tac HOL_cs);
by (  contr_tac 2);
by ( fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
qed "slen_scons_eq_rev";

Goal "!x. Fin n < #x = (stream_take n\\<cdot>x ~= x)";
by (nat_ind_tac "n" 1);
by  (simp_tac(simpset() addsimps [slen_empty_eq, thm "Fin_0"]) 1);
by  (Fast_tac 1);
by (rtac allI 1);
by (asm_simp_tac (simpset() addsimps [slen_scons_eq]) 1);
by (etac thin_rl 1);
by (safe_tac HOL_cs);
by  (Asm_full_simp_tac 1);
by (stream_case_tac "x" 1);
by (rotate_tac ~1 2);
by Auto_tac;
qed_spec_mp "slen_take_eq";

Goalw [thm "ile_def"] "#x <= Fin n = (stream_take n\\<cdot>x = x)";
by (simp_tac (simpset() addsimps [slen_take_eq]) 1);
qed "slen_take_eq_rev";

Goal "#x = Fin n ==> stream_take n\\<cdot>x = x";
by (asm_simp_tac (simpset() addsimps [slen_take_eq_rev RS sym]) 1);
qed "slen_take_lemma1";

Goal "!x. ~stream_finite x --> #(stream_take i\\<cdot>x) = Fin i";
by (nat_ind_tac "i" 1);
by  (simp_tac(simpset() addsimps [thm "Fin_0"]) 1);
by (rtac allI 1);
by (stream_case_tac "x" 1);
by  (auto_tac (claset()addSIs [stream_finite_lemma1], simpset() delsimps [thm "iSuc_Fin"] addsimps [thm "iSuc_Fin" RS sym]));
by (force_tac (claset(), simpset() addsimps [stream.finite_def]) 1);
qed_spec_mp "slen_take_lemma2";

Goal "stream_finite x = (#x ~= Infty)";
by (rtac iffI 1);
by  (etac stream_finite_ind 1);
by   (Simp_tac 1);
by  (etac (slen_scons RS ssubst) 1);
by  (stac (thm "iSuc_Infty" RS sym) 1);
by  (etac contrapos_nn 1);
by  (etac (thm "iSuc_inject" RS iffD1) 1);
by (case_tac "#x" 1);
by (auto_tac (claset()addSDs [slen_take_lemma1],
        simpset() addsimps [stream.finite_def]));
qed "slen_infinite";

Goal "s << t ==> #s <= #t";
by (case_tac "stream_finite t" 1);
by  (EVERY'[dtac (slen_infinite RS subst), dtac notnotD] 2);
by  (Asm_simp_tac 2);
by (etac rev_mp 1);
by (res_inst_tac [("x","s")] allE 1);
by  (atac 2);
by (etac (stream_finite_ind) 1);
by  (Simp_tac 1);
by (rtac allI 1);
by (stream_case_tac "x" 1);
by  (asm_simp_tac (HOL_ss addsimps [slen_empty, thm "i0_lb"]) 1);
by (asm_simp_tac (HOL_ss addsimps [slen_scons]) 1);
by (fast_tac(claset() addSIs [thm "iSuc_ile_mono" RS iffD2] addSDs stream.inverts) 1);
qed "slen_mono";

Goal "!(x::'a::flat stream) y. Fin n <= #x --> x << y --> \
\ stream_take n\\<cdot>x = stream_take n\\<cdot>y";
by (nat_ind_tac "n" 1);
by ( simp_tac(simpset() addsimps [slen_empty_eq]) 1);
by (strip_tac 1);
by (stream_case_tac "x" 1);
by  (asm_full_simp_tac (HOL_ss addsimps [slen_empty, 
              thm "iSuc_Fin" RS sym, thm "not_iSuc_ilei0"]) 1);
by (fatac stream_prefix 1 1);
by (safe_tac (claset() addSDs [stream_flat_prefix]));
by (Simp_tac 1);
by (rtac cfun_arg_cong 1);
by (rotate_tac 3 1);
by (asm_full_simp_tac (simpset() delsimps [thm "iSuc_Fin"] addsimps 
        [thm "iSuc_Fin" RS sym, thm "iSuc_ile_mono"]) 1);
qed_spec_mp "slen_take_lemma3";

Goal "stream_finite t ==> \
\!s. #(s::'a::flat stream) = #t &  s << t --> s = t";
by (etac stream_finite_ind 1);
by  (fast_tac (claset() addDs [eq_UU_iff RS iffD2]) 1);
by (Safe_tac);
by (stream_case_tac "sa" 1);
by  (dtac sym 1);
by  (Asm_full_simp_tac 1);
by (safe_tac (claset() addSDs [stream_flat_prefix]));
by (rtac cfun_arg_cong 1);
by (etac allE 1);
by (etac mp 1);
by (Asm_full_simp_tac 1);
qed "slen_strict_mono_lemma";

Goal "[|stream_finite t; s ~= t; s << (t::'a::flat stream) |] ==> #s < #t";
by (rtac (thm "ilessI1") 1);
by  (etac slen_mono 1);
by (dtac slen_strict_mono_lemma 1);
by (Fast_tac 1);
qed "slen_strict_mono";

Goal "!x. Fin (i + j) <= #x --> Fin j <= #(iterate i rt x)";
by (nat_ind_tac "i" 1);
by  (Simp_tac 1);
by (strip_tac 1);
by (stream_case_tac "x" 1);
by  (asm_full_simp_tac (simpset() delsimps [thm "iSuc_Fin"] 
             addsimps [thm "iSuc_Fin" RS sym]) 1);
by (stac iterate_Suc2 1);
by (rotate_tac 2 1);
by (asm_full_simp_tac  (simpset() delsimps [thm "iSuc_Fin"] 
    addsimps [thm "iSuc_Fin" RS sym, thm "iSuc_ile_mono"]) 1);
qed_spec_mp "slen_rt_mult";


(* ------------------------------------------------------------------------- *)

section "sfilter";

bind_thm ("sfilter_unfold", fix_prover2 thy sfilter_def 
	"sfilter = (\\<Lambda>p s. case s of x && xs => \
\  If p\\<cdot>x then x && sfilter\\<cdot>p\\<cdot>xs else sfilter\\<cdot>p\\<cdot>xs fi)");

Goal "sfilter\\<cdot>\\<bottom> = \\<bottom>";
by (rtac ext_cfun 1);
by (stac sfilter_unfold 1);
by (stream_case_tac "x" 1);
by  Auto_tac;
qed "strict_sfilter";

Goal "sfilter\\<cdot>f\\<cdot>\\<bottom> = \\<bottom>";
by (stac sfilter_unfold 1);
by (Simp_tac 1);
qed "sfilter_empty";

Goal "x ~= \\<bottom> ==> sfilter\\<cdot>f\\<cdot>(x && xs) = \
\ If f\\<cdot>x then x && sfilter\\<cdot>f\\<cdot>xs else sfilter\\<cdot>f\\<cdot>xs fi";
by (rtac trans 1);
by (stac sfilter_unfold 1);
by (Asm_simp_tac 1);
by (rtac refl 1);
qed "sfilter_scons";

