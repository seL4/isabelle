(*  Title:	HOLCF/ex/hoare.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright	1993 Technische Universitaet Muenchen
*)

open Hoare;

(* --------- pure HOLCF logic, some little lemmas ------ *)

qed_goal "hoare_lemma2" HOLCF.thy "~b=TT ==> b=FF | b=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (Exh_tr RS disjE) 1),
	(fast_tac HOL_cs 1),
	(etac disjE 1),
	(contr_tac 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "hoare_lemma3" HOLCF.thy 
" (!k.b1[iterate(k,g,x)]=TT) | (? k.~ b1[iterate(k,g,x)]=TT)"
 (fn prems =>
	[
	(fast_tac HOL_cs 1)
	]);

qed_goal "hoare_lemma4" HOLCF.thy 
"(? k.~ b1[iterate(k,g,x)]=TT) ==> \
\ ? k.b1[iterate(k,g,x)]=FF | b1[iterate(k,g,x)]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(rtac exI 1),
	(rtac hoare_lemma2 1),
	(atac 1)
	]);

qed_goal "hoare_lemma5" HOLCF.thy 
"[|(? k.~ b1[iterate(k,g,x)]=TT);\
\   k=theleast(%n.~ b1[iterate(n,g,x)]=TT)|] ==> \
\ b1[iterate(k,g,x)]=FF | b1[iterate(k,g,x)]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(rtac hoare_lemma2 1),
	(etac exE 1),
	(etac theleast1 1)
	]);

qed_goal "hoare_lemma6" HOLCF.thy "b=UU ==> ~b=TT"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(resolve_tac dist_eq_tr 1)
	]);

qed_goal "hoare_lemma7" HOLCF.thy "b=FF ==> ~b=TT"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(resolve_tac dist_eq_tr 1)
	]);

qed_goal "hoare_lemma8" HOLCF.thy 
"[|(? k.~ b1[iterate(k,g,x)]=TT);\
\   k=theleast(%n.~ b1[iterate(n,g,x)]=TT)|] ==> \
\ !m. m<k --> b1[iterate(m,g,x)]=TT"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(etac exE 1),
	(strip_tac 1),
	(res_inst_tac [("p","b1[iterate(m,g,x)]")] trE 1),
	(atac 2),
	(rtac (le_less_trans RS less_anti_refl) 1),
	(atac 2),
	(rtac theleast2 1),
	(etac hoare_lemma6 1),
	(rtac (le_less_trans RS less_anti_refl) 1),
	(atac 2),
	(rtac theleast2 1),
	(etac hoare_lemma7 1)
	]);

qed_goal "hoare_lemma28" HOLCF.thy 
"b1[y::'a]=(UU::tr) ==> b1[UU] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac (flat_tr RS flat_codom RS disjE) 1),
	(atac 1),
	(etac spec 1)
	]);


(* ----- access to definitions ----- *)

qed_goalw "p_def2" Hoare.thy [p_def]
"p = fix[LAM f x. If b1[x] then f[g[x]] else x fi]"
 (fn prems =>
	[
	(rtac refl 1)
	]);

qed_goalw "q_def2" Hoare.thy [q_def]
"q = fix[LAM f x. If b1[x] orelse b2[x] then \
\     f[g[x]] else x fi]"
 (fn prems =>
	[
	(rtac refl 1)
	]);


qed_goal "p_def3" Hoare.thy 
"p[x] = If b1[x] then p[g[x]] else x fi"
 (fn prems =>
	[
	(fix_tac3 p_def 1),
	(simp_tac HOLCF_ss 1)
	]);

qed_goal "q_def3" Hoare.thy 
"q[x] = If b1[x] orelse b2[x] then q[g[x]] else x fi"
 (fn prems =>
	[
	(fix_tac3 q_def 1),
	(simp_tac HOLCF_ss 1)
	]);

(** --------- proves about iterations of p and q ---------- **)

qed_goal "hoare_lemma9" Hoare.thy 
"(! m. m<Suc(k) --> b1[iterate(m,g,x)]=TT) -->\
\  p[iterate(k,g,x)]=p[x]"
 (fn prems =>
	[
	(nat_ind_tac "k" 1),
	(simp_tac iterate_ss 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(res_inst_tac [("s","p[iterate(k1,g,x)]")] trans 1),
	(rtac trans 1),
	(rtac (p_def3 RS sym) 2),
	(res_inst_tac [("s","TT"),("t","b1[iterate(k1,g,x)]")] ssubst 1),
	(rtac mp 1),
	(etac spec 1),
	(simp_tac nat_ss 1),
	(simp_tac HOLCF_ss 1),
	(etac mp 1),
	(strip_tac 1),
	(rtac mp 1),
	(etac spec 1),
	(etac less_trans 1),
	(simp_tac nat_ss 1)
	]);

qed_goal "hoare_lemma24" Hoare.thy 
"(! m. m<Suc(k) --> b1[iterate(m,g,x)]=TT) --> \
\ q[iterate(k,g,x)]=q[x]"
 (fn prems =>
	[
	(nat_ind_tac "k" 1),
	(simp_tac iterate_ss 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(res_inst_tac [("s","q[iterate(k1,g,x)]")] trans 1),
	(rtac trans 1),
	(rtac (q_def3 RS sym) 2),
	(res_inst_tac [("s","TT"),("t","b1[iterate(k1,g,x)]")] ssubst 1),
	(rtac mp 1),
	(etac spec 1),
	(simp_tac nat_ss 1),
	(simp_tac HOLCF_ss 1),
	(etac mp 1),
	(strip_tac 1),
	(rtac mp 1),
	(etac spec 1),
	(etac less_trans 1),
	(simp_tac nat_ss 1)
	]);

(* -------- results about p for case (? k.~ b1[iterate(k,g,x)]=TT) ------- *)


val hoare_lemma10 = (hoare_lemma8 RS (hoare_lemma9 RS mp));
(* 
[| ? k. ~ b1[iterate(k,g,?x1)] = TT;
   Suc(?k3) = theleast(%n. ~ b1[iterate(n,g,?x1)] = TT) |] ==>
p[iterate(?k3,g,?x1)] = p[?x1]
*)

qed_goal "hoare_lemma11" Hoare.thy 
"(? n.b1[iterate(n,g,x)]~=TT) ==>\
\ k=theleast(%n.b1[iterate(n,g,x)]~=TT) & b1[iterate(k,g,x)]=FF \
\ --> p[x] = iterate(k,g,x)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("n","k")] natE 1),
	(hyp_subst_tac 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac trans 1),
	(rtac p_def3 1),
	(asm_simp_tac HOLCF_ss  1),
	(eres_inst_tac [("s","0"),("t","theleast(%n. b1[iterate(n, g, x)] ~= TT)")]
	subst 1),
	(simp_tac iterate_ss 1),
	(hyp_subst_tac 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac trans 1),
	(etac (hoare_lemma10 RS sym) 1),
	(atac 1),
	(rtac trans 1),
	(rtac p_def3 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(xa,g,x)]")] ssubst 1),
	(rtac (hoare_lemma8 RS spec RS mp) 1),
	(atac 1),
	(atac 1),
	(simp_tac nat_ss 1),
	(simp_tac HOLCF_ss 1),
	(rtac trans 1),
	(rtac p_def3 1),
	(simp_tac (HOLCF_ss addsimps [iterate_Suc RS sym]) 1),
	(eres_inst_tac [("s","FF")]	ssubst 1),
	(simp_tac HOLCF_ss 1)
	]);

qed_goal "hoare_lemma12" Hoare.thy 
"(? n.~ b1[iterate(n,g,x)]=TT) ==>\
\ k=theleast(%n.~ b1[iterate(n,g,x)]=TT) & b1[iterate(k,g,x)]=UU \
\ --> p[x] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("n","k")] natE 1),
	(hyp_subst_tac 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac trans 1),
	(rtac p_def3 1),
	(asm_simp_tac HOLCF_ss  1),
	(hyp_subst_tac 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac trans 1),
	(rtac (hoare_lemma10 RS sym) 1),
	(atac 1),
	(atac 1),
	(rtac trans 1),
	(rtac p_def3 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(xa,g,x)]")] ssubst 1),
	(rtac (hoare_lemma8 RS spec RS mp) 1),
	(atac 1),
	(atac 1),
	(simp_tac nat_ss 1),
	(asm_simp_tac HOLCF_ss  1),
	(rtac trans 1),
	(rtac p_def3 1),
	(asm_simp_tac HOLCF_ss  1)
	]);

(* -------- results about p for case  (! k. b1[iterate(k,g,x)]=TT) ------- *)

qed_goal "fernpass_lemma" Hoare.thy 
"(! k. b1[iterate(k,g,x)]=TT) ==> !k.p[iterate(k,g,x)] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (p_def2 RS ssubst) 1),
	(rtac fix_ind 1),
	(rtac adm_all 1),
	(rtac allI 1),
	(rtac adm_eq 1),
	(contX_tacR 1),
	(rtac allI 1),
	(rtac (strict_fapp1 RS ssubst) 1),
	(rtac refl 1),
	(simp_tac iterate_ss 1),
	(rtac allI 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(k,g,x)]")] ssubst 1),
	(etac spec 1),
	(asm_simp_tac HOLCF_ss 1),
	(rtac (iterate_Suc RS subst) 1),
	(etac spec 1)
	]);

qed_goal "hoare_lemma16" Hoare.thy 
"(! k. b1[iterate(k,g,x)]=TT) ==> p[x] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("F1","g"),("t","x")] (iterate_0 RS subst) 1),
	(etac (fernpass_lemma RS spec) 1)
	]);

(* -------- results about q for case  (! k. b1[iterate(k,g,x)]=TT) ------- *)

qed_goal "hoare_lemma17" Hoare.thy 
"(! k. b1[iterate(k,g,x)]=TT) ==> !k.q[iterate(k,g,x)] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (q_def2 RS ssubst) 1),
	(rtac fix_ind 1),
	(rtac adm_all 1),
	(rtac allI 1),
	(rtac adm_eq 1),
	(contX_tacR 1),
	(rtac allI 1),
	(rtac (strict_fapp1 RS ssubst) 1),
	(rtac refl 1),
	(rtac allI 1),
	(simp_tac iterate_ss 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(k,g,x)]")] ssubst 1),
	(etac spec 1),
	(asm_simp_tac HOLCF_ss  1),
	(rtac (iterate_Suc RS subst) 1),
	(etac spec 1)
	]);

qed_goal "hoare_lemma18" Hoare.thy 
"(! k. b1[iterate(k,g,x)]=TT) ==> q[x] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("F1","g"),("t","x")] (iterate_0 RS subst) 1),
	(etac (hoare_lemma17 RS spec) 1)
	]);

qed_goal "hoare_lemma19" Hoare.thy 
"(!k. (b1::'a->tr)[iterate(k,g,x)]=TT) ==> b1[UU::'a] = UU | (!y.b1[y::'a]=TT)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (flat_tr RS flat_codom) 1),
	(res_inst_tac [("t","x1")] (iterate_0 RS subst) 1),
	(etac spec 1)
	]);

qed_goal "hoare_lemma20" Hoare.thy 
"(! y. b1[y::'a]=TT) ==> !k.q[iterate(k,g,x::'a)] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (q_def2 RS ssubst) 1),
	(rtac fix_ind 1),
	(rtac adm_all 1),
	(rtac allI 1),
	(rtac adm_eq 1),
	(contX_tacR 1),
	(rtac allI 1),
	(rtac (strict_fapp1 RS ssubst) 1),
	(rtac refl 1),
	(rtac allI 1),
	(simp_tac iterate_ss 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(k,g,x::'a)]")] ssubst 1),
	(etac spec 1),
	(asm_simp_tac HOLCF_ss  1),
	(rtac (iterate_Suc RS subst) 1),
	(etac spec 1)
	]);

qed_goal "hoare_lemma21" Hoare.thy 
"(! y. b1[y::'a]=TT) ==> q[x::'a] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("F1","g"),("t","x")] (iterate_0 RS subst) 1),
	(etac (hoare_lemma20 RS spec) 1)
	]);

qed_goal "hoare_lemma22" Hoare.thy 
"b1[UU::'a]=UU ==> q[UU::'a] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (q_def3 RS ssubst) 1),
	(asm_simp_tac HOLCF_ss  1)
	]);

(* -------- results about q for case (? k.~ b1[iterate(k,g,x)]=TT) ------- *)

val hoare_lemma25 = (hoare_lemma8 RS (hoare_lemma24 RS mp) );
(* 
[| ? k. ~ ?b1.1[iterate(k,?g1,?x1)] = TT;
   Suc(?k3) = theleast(%n. ~ ?b1.1[iterate(n,?g1,?x1)] = TT) |] ==>
q[iterate(?k3,?g1,?x1)] = q[?x1]
*)

qed_goal "hoare_lemma26" Hoare.thy 
"(? n.~ b1[iterate(n,g,x)]=TT) ==>\
\ k=theleast(%n.~ b1[iterate(n,g,x)]=TT) & b1[iterate(k,g,x)]=FF \
\ --> q[x] = q[iterate(k,g,x)]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("n","k")] natE 1),
	(hyp_subst_tac 1),
	(strip_tac 1),
	(simp_tac iterate_ss 1),
	(hyp_subst_tac 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac trans 1),
	(rtac (hoare_lemma25 RS sym) 1),
	(atac 1),
	(atac 1),
	(rtac trans 1),
	(rtac q_def3 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(xa,g,x)]")] ssubst 1),
	(rtac (hoare_lemma8 RS spec RS mp) 1),
	(atac 1),
	(atac 1),
	(simp_tac nat_ss 1),
	(simp_tac (HOLCF_ss addsimps [iterate_Suc]) 1)
	]);


qed_goal "hoare_lemma27" Hoare.thy 
"(? n.~ b1[iterate(n,g,x)]=TT) ==>\
\ k=theleast(%n.~ b1[iterate(n,g,x)]=TT) & b1[iterate(k,g,x)]=UU \
\ --> q[x] = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("n","k")] natE 1),
	(hyp_subst_tac 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac (q_def3 RS ssubst) 1),
	(asm_simp_tac HOLCF_ss  1),
	(hyp_subst_tac 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(rtac trans 1),
	(rtac (hoare_lemma25 RS sym) 1),
	(atac 1),
	(atac 1),
	(rtac trans 1),
	(rtac q_def3 1),
	(res_inst_tac [("s","TT"),("t","b1[iterate(xa,g,x)]")] ssubst 1),
	(rtac (hoare_lemma8 RS spec RS mp) 1),
	(atac 1),
	(atac 1),
	(simp_tac nat_ss 1),
	(asm_simp_tac HOLCF_ss 1),
	(rtac trans 1),
	(rtac q_def3 1),
	(asm_simp_tac HOLCF_ss  1)
	]);

(* ------- (! k. b1[iterate(k,g,x)]=TT) ==> q o p = q   ----- *)

qed_goal "hoare_lemma23" Hoare.thy 
"(! k. b1[iterate(k,g,x)]=TT) ==> q[p[x]] = q[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (hoare_lemma16 RS ssubst) 1),
	(atac 1),
	(rtac (hoare_lemma19 RS disjE) 1),
	(atac 1),
	(rtac (hoare_lemma18 RS ssubst) 1),
	(atac 1),
	(rtac (hoare_lemma22 RS ssubst) 1),
	(atac 1),
	(rtac refl 1),
	(rtac (hoare_lemma21 RS ssubst) 1),
	(atac 1),
	(rtac (hoare_lemma21 RS ssubst) 1),
	(atac 1),
	(rtac refl 1)
	]);

(* ------------  ? k. ~ b1[iterate(k,g,x)] = TT ==> q o p = q   ----- *)

qed_goal "hoare_lemma29" Hoare.thy 
"? k. ~ b1[iterate(k,g,x)] = TT ==> q[p[x]] = q[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (hoare_lemma5 RS disjE) 1),
	(atac 1),
	(rtac refl 1),
	(rtac (hoare_lemma11 RS mp RS ssubst) 1),
	(atac 1),
	(rtac conjI 1),
	(rtac refl 1),
	(atac 1),
	(rtac (hoare_lemma26 RS mp RS subst) 1),
	(atac 1),
	(rtac conjI 1),
	(rtac refl 1),
	(atac 1),
	(rtac refl 1),
	(rtac (hoare_lemma12 RS mp RS ssubst) 1),
	(atac 1),
	(rtac conjI 1),
	(rtac refl 1),
	(atac 1),
	(rtac (hoare_lemma22 RS ssubst) 1),
	(rtac (hoare_lemma28 RS ssubst) 1),
	(atac 1),
	(rtac refl 1),
	(rtac sym 1),
	(rtac (hoare_lemma27 RS mp RS ssubst) 1),
	(atac 1),
	(rtac conjI 1),
	(rtac refl 1),
	(atac 1),
	(rtac refl 1)
	]);

(* ------ the main prove q o p = q ------ *)

qed_goal "hoare_main" Hoare.thy "q oo p = q"
 (fn prems =>
	[
	(rtac ext_cfun 1),
	(rtac (cfcomp2 RS ssubst) 1),
	(rtac (hoare_lemma3 RS disjE) 1),
	(etac hoare_lemma23 1),
	(etac hoare_lemma29 1)
	]);


