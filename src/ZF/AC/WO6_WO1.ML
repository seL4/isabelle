(*  Title: 	ZF/AC/WO6_WO1.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

The proof of "WO6 ==> WO1".

From the book "Equivalents of the Axiom of Choice" by Rubin & Rubin,
pages 2-5
*)

(* ********************************************************************** *)
(* The most complicated part of the proof - lemma ii - p. 2-4		  *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* some properties of relation uu(beta, gamma, delta) - p. 2		  *)
(* ********************************************************************** *)

goalw thy [uu_def] "domain(uu(f,b,g,d)) <= f`b";
by (fast_tac ZF_cs 1);
val domain_uu_subset = result();

goal thy "!!a. [| ALL b<a. f`b lepoll m; b<a |]  \
\		==> domain(uu(f, b, g, d)) lepoll m";
by (fast_tac (AC_cs addSEs
	[domain_uu_subset RS subset_imp_lepoll RS lepoll_trans]) 1);
val domain_uu_lepoll_m = result();

goal thy "!! a. ALL b<a. f`b lepoll m ==> \
\          ALL b<a. ALL g<a. ALL d<a. domain(uu(f,b,g,d)) lepoll m";
by (fast_tac (AC_cs addEs [domain_uu_lepoll_m]) 1);
val quant_domain_uu_lepoll_m = result();

(* used in case 2 *)
goalw thy [uu_def] "uu(f,b,g,d) <= f`b * f`g";
by (fast_tac ZF_cs 1);
val uu_subset1 = result();

goalw thy [uu_def] "uu(f,b,g,d) <= f`d";
by (fast_tac ZF_cs 1);
val uu_subset2 = result();

goal thy "!! a. [| ALL b<a. f`b lepoll m; d<a |] ==> uu(f,b,g,d) lepoll m";
by (fast_tac (AC_cs
	addSEs [uu_subset2 RS subset_imp_lepoll RS lepoll_trans]) 1);
val uu_lepoll_m = result();

(* ********************************************************************** *)
(* Two cases for lemma ii 						  *)
(* ********************************************************************** *)
goalw thy [lesspoll_def] 
  "!! a f u. ALL b<a. ALL g<a. ALL d<a. u(f,b,g,d) lepoll m ==>  \
\ (ALL b<a. f`b ~= 0 --> (EX g<a. EX d<a. u(f,b,g,d) ~= 0 &  \
\				u(f,b,g,d) lesspoll m)) |  \
\ (EX b<a. f`b ~= 0 & (ALL g<a. ALL d<a. u(f,b,g,d) ~= 0 -->  \
\				u(f,b,g,d) eqpoll m))";
by (fast_tac AC_cs 1);
val cases = result();

(* ********************************************************************** *)
(* Lemmas used in both cases						  *)
(* ********************************************************************** *)
goal thy "!!a f. Ord(a) ==> (UN b<a++a. f`b) = (UN b<a. f`b Un f`(a++b))";
by (resolve_tac [equalityI] 1);
by (fast_tac (AC_cs addIs [ltI, OUN_I] addSEs [OUN_E]
		addSDs [lt_oadd_disj]) 1);
by (fast_tac (AC_cs addSEs [lt_oadd1, oadd_lt_mono2, OUN_E]
		addSIs [OUN_I]) 1);
val UN_oadd = result();

val [prem] = goal thy
	"(!!b. b<a ==> P(b)=Q(b)) ==> (UN b<a. P(b)) = (UN b<a. Q(b))";
by (fast_tac (ZF_cs addSIs [OUN_I, equalityI] 
		addSEs [OUN_E, prem RS equalityD1 RS subsetD, 
			prem RS sym RS equalityD1 RS subsetD]) 1);
val UN_eq = result();

goal thy "!!a. b<a ==> b = (THE l. l<a & a ++ b = a ++ l)";
by (fast_tac (ZF_cs addSIs [the_equality RS sym] 
                    addIs [lt_Ord2, lt_Ord] 
                    addSEs [oadd_inject RS sym]) 1);
val the_only_b = result();

goal thy "!!A. B <= A ==> B Un (A-B) = A";
by (fast_tac (ZF_cs addSIs [equalityI]) 1);
val subset_imp_Un_Diff_eq = result();

(* ********************************************************************** *)
(* Case 1 : lemmas							  *)
(* ********************************************************************** *)

goalw thy [vv1_def] "vv1(f,b,succ(m)) <= f`b";
by (resolve_tac [expand_if RS iffD2] 1);
by (fast_tac (ZF_cs addSIs [domain_uu_subset]) 1);
val vv1_subset = result();

(* ********************************************************************** *)
(* Case 1 : Union of images is the whole "y"				  *)
(* ********************************************************************** *)
goal thy "!! a f y. [| (UN b<a. f`b) = y; Ord(a); m:nat |] ==>  \
\	(UN b<a++a. (lam b:a++a. if(b<a, vv1(f,b,succ(m)),  \
\			ww1(f, THE l. l<a & b=a++l, succ(m)))) ` b) = y";
by (resolve_tac [UN_oadd RS ssubst] 1 THEN (atac 1));
by (eresolve_tac [subst] 1);
by (resolve_tac [UN_eq] 1);
by (forw_inst_tac [("i","a")] lt_oadd1 1
	THEN (REPEAT (atac 1)));
by (forw_inst_tac [("j","a")] oadd_lt_mono2 1
	THEN (REPEAT (atac 1)));
by (asm_simp_tac (ZF_ss addsimps [ltD RS beta,
	oadd_le_self RS le_imp_not_lt RS if_not_P, lt_Ord]) 1);
by (resolve_tac [the_only_b RS subst] 1 THEN (atac 1));
by (asm_simp_tac (ZF_ss 
	addsimps [vv1_subset RS subset_imp_Un_Diff_eq, ltD, ww1_def]) 1);
val UN_eq_y = result();

(* ********************************************************************** *)
(* every value of defined function is less than or equipollent to m	  *)
(* ********************************************************************** *)
goal thy "!!a b. [| P(a, b); Ord(a); Ord(b);  \
\		Least_a = (LEAST a. EX x. Ord(x) & P(a, x)) |]  \
\		==> P(Least_a, LEAST b. P(Least_a, b))";
by (eresolve_tac [ssubst] 1);
by (res_inst_tac [("Q","%z. P(z, LEAST b. P(z, b))")] LeastI2 1);
by (REPEAT (fast_tac (ZF_cs addSEs [LeastI]) 1));
val nested_LeastI = result();

val nested_Least_instance = read_instantiate 
	[("P","%g d. domain(uu(f,b,g,d)) ~= 0 &  \
\		domain(uu(f,b,g,d)) lesspoll succ(m)")] nested_LeastI;

goalw thy [vv1_def] "!!a. [| ALL b<a. f`b ~=0 -->  \
\		(EX g<a. EX d<a. domain(uu(f,b,g,d))~=0 &  \
\		domain(uu(f,b,g,d)) lesspoll succ(m)); m:nat; b<a |]  \
\		==> vv1(f,b,succ(m)) lesspoll succ(m)";
by (resolve_tac [expand_if RS iffD2] 1);
by (fast_tac (AC_cs addIs [nested_Least_instance RS conjunct2]
		addSEs [lt_Ord]
		addSIs [empty_lepollI RS lepoll_imp_lesspoll_succ]) 1);
val vv1_lesspoll_succ = result();

goalw thy [vv1_def] "!!a. [| ALL b<a. f`b ~=0 -->  \
\	(EX g<a. EX d<a. domain(uu(f,b,g,d))~=0 &  \
\	domain(uu(f,b,g,d)) lesspoll succ(m)); m:nat; b<a; f`b ~= 0 |]  \
\	==> vv1(f,b,succ(m)) ~= 0";
by (resolve_tac [expand_if RS iffD2] 1);
by (resolve_tac [conjI] 1);
by (fast_tac ZF_cs 2);
by (resolve_tac [impI] 1);
by (eresolve_tac [oallE] 1);
by (mp_tac 1);
by (contr_tac 2);
by (REPEAT (eresolve_tac [oexE] 1));
by (asm_simp_tac (ZF_ss
	addsimps [lt_Ord, nested_Least_instance RS conjunct1]) 1);
val vv1_not_0 = result();

goalw thy [ww1_def] "!!a. [| ALL b<a. f`b ~=0 -->  \
\	(EX g<a. EX d<a. domain(uu(f,b,g,d))~=0 &  \
\	domain(uu(f,b,g,d)) lesspoll succ(m));  \
\	ALL b<a. f`b lepoll succ(m); m:nat; b<a  |]  \
\	==> ww1(f,b,succ(m)) lesspoll succ(m)";
by (excluded_middle_tac "f`b = 0" 1);
by (asm_full_simp_tac (AC_ss
	addsimps [empty_lepollI RS lepoll_imp_lesspoll_succ]) 2);
by (resolve_tac [Diff_lepoll RS lepoll_imp_lesspoll_succ] 1);
by (fast_tac AC_cs 1);
by (REPEAT (ares_tac [vv1_subset, vv1_not_0] 1));
val ww1_lesspoll_succ = result();

goal thy "!!a. [| Ord(a); m:nat;  \
\	ALL b<a. f`b ~=0 --> (EX g<a. EX d<a. domain(uu(f,b,g,d))~=0 &  \
\			domain(uu(f,b,g,d)) lesspoll succ(m));  \
\	ALL b<a. f`b lepoll succ(m) |]  \
\	==> ALL b<a++a. (lam b:a++a. if(b<a, vv1(f,b,succ(m)),  \
\		ww1(f,THE l. l<a & b = a ++ l,succ(m))))`b lepoll m";
by (resolve_tac [oallI] 1);
by (asm_full_simp_tac (ZF_ss addsimps [ltD RS beta]) 1);
by (resolve_tac [lesspoll_succ_imp_lepoll] 1 THEN (atac 2));
by (resolve_tac [expand_if RS iffD2] 1);
by (resolve_tac [conjI] 1);
by (resolve_tac [impI] 1);
by (forward_tac [lt_oadd_disj1] 2 THEN (REPEAT (atac 2)));
by (resolve_tac [impI] 2);
by (eresolve_tac [disjE] 2 THEN (fast_tac (ZF_cs addSEs [ltE]) 2));
by (asm_full_simp_tac (ZF_ss addsimps [vv1_lesspoll_succ]) 1);
by (dresolve_tac [theI] 1);
by (eresolve_tac [conjE] 1);
by (resolve_tac [ww1_lesspoll_succ] 1 THEN (REPEAT (atac 1)));
val all_sum_lepoll_m = result();

(* ********************************************************************** *)
(* Case 2 : lemmas							  *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* Case 2 : vv2_subset							  *)
(* ********************************************************************** *)

goalw thy [uu_def] "!!f. [| b<a; g<a; f`b~=0; f`g~=0;  \
\			y*y <= y; (UN b<a. f`b)=y |]  \
\			==> EX d<a. uu(f,b,g,d)~=0";
by (fast_tac (AC_cs addSIs [not_emptyI] 
		addSDs [SigmaI RSN (2, subsetD)]
		addSEs [not_emptyE]) 1);
val ex_d_uu_not_empty = result();

goal thy "!!f. [| b<a; g<a; f`b~=0; f`g~=0;  \
\			y*y<=y;	(UN b<a. f`b)=y |]  \
\		==> uu(f,b,g,LEAST d. (uu(f,b,g,d) ~= 0)) ~= 0";
by (dresolve_tac [ex_d_uu_not_empty] 1 THEN (REPEAT (atac 1)));
by (fast_tac (AC_cs addSEs [LeastI, lt_Ord]) 1);
val uu_not_empty = result();

(* moved from ZF_aux.ML *)
goal thy "!!r. [| r<=A*B; r~=0 |] ==> domain(r)~=0";
by (REPEAT (eresolve_tac [asm_rl, not_emptyE, subsetD RS SigmaE, 
		sym RSN (2, subst_elem) RS domainI RS not_emptyI] 1));
val not_empty_rel_imp_domain = result();

goal thy "!!f. [| b<a; g<a; f`b~=0; f`g~=0;  \
\			y*y <= y; (UN b<a. f`b)=y |]  \
\		==> (LEAST d. uu(f,b,g,d) ~= 0) < a";
by (eresolve_tac [ex_d_uu_not_empty RS oexE] 1
	THEN (REPEAT (atac 1)));
by (resolve_tac [Least_le RS lt_trans1] 1
	THEN (REPEAT (ares_tac [lt_Ord] 1)));
val Least_uu_not_empty_lt_a = result();

goal thy "!!B. [| B<=A; a~:B |] ==> B <= A-{a}";
by (fast_tac ZF_cs 1);
val subset_Diff_sing = result();

goal thy "!!A B. [| A lepoll m; m lepoll B; B <= A; m:nat |] ==> A=B";
by (eresolve_tac [natE] 1);
by (fast_tac (AC_cs addSDs [lepoll_0_is_0] addSIs [equalityI]) 1);
by (hyp_subst_tac 1);
by (resolve_tac [equalityI] 1);
by (atac 2);
by (resolve_tac [subsetI] 1);
by (excluded_middle_tac "?P" 1 THEN (atac 2));
by (eresolve_tac [subset_Diff_sing RS subset_imp_lepoll RSN (2, 
		diff_sing_lepoll RSN (3, lepoll_trans RS lepoll_trans)) RS 
		succ_lepoll_natE] 1
	THEN (REPEAT (atac 1)));
val supset_lepoll_imp_eq = result();

goalw thy [vv2_def] 
	"!!a. [| ALL g<a. ALL d<a. domain(uu(f, b, g, d))~=0 -->  \
\	domain(uu(f, b, g, d)) eqpoll succ(m);  \
\	ALL b<a. f`b lepoll succ(m); y*y <= y;  \
\	(UN b<a. f`b)=y; b<a; g<a; d<a; f`b~=0; f`g~=0; m:nat; aa:f`b |]  \
\	 ==> uu(f,b,g,LEAST d. uu(f,b,g,d)~=0) : f`b -> f`g";
by (eres_inst_tac [("x","g")] oallE 1 THEN (contr_tac 2));
by (eres_inst_tac [("P","%z. ?QQ(z) ~= 0 --> ?RR(z)")] oallE 1);
by (eresolve_tac [impE] 1);
by (eresolve_tac [uu_not_empty RS (uu_subset1 RS 
	not_empty_rel_imp_domain)] 1
	THEN (REPEAT (atac 1)));
by (eresolve_tac [Least_uu_not_empty_lt_a RSN (2, notE)] 2
	THEN (TRYALL atac));
by (resolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RS 
	(Least_uu_not_empty_lt_a RSN (2, uu_lepoll_m) RSN (2, 
	uu_subset1 RSN (4, rel_is_fun)))] 1
	THEN (TRYALL atac));
by (resolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RSN (2, 
		supset_lepoll_imp_eq)] 1);
by (REPEAT (fast_tac (AC_cs addSIs [domain_uu_subset, nat_succI]) 1));
val uu_Least_is_fun = result();

goalw thy [vv2_def]
	"!!a. [| ALL g<a. ALL d<a. domain(uu(f, b, g, d))~=0 -->  \
\		domain(uu(f, b, g, d)) eqpoll succ(m);  \
\		ALL b<a. f`b lepoll succ(m); y*y <= y;  \
\		(UN b<a. f`b)=y; b<a; g<a; m:nat; aa:f`b |]  \
\		==> vv2(f,b,g,aa) <= f`g";
by (fast_tac (FOL_cs addIs [expand_if RS iffD2]
	addSEs [uu_Least_is_fun]
	addSIs [empty_subsetI, not_emptyI, 
		singleton_subsetI, apply_type]) 1);
val vv2_subset = result();

(* ********************************************************************** *)
(* Case 2 : Union of images is the whole "y"				  *)
(* ********************************************************************** *)
goal thy "!!a. [| ALL g<a. ALL d<a. domain(uu(f,b,g,d)) ~= 0 -->  \
\	domain(uu(f,b,g,d)) eqpoll succ(m);  \
\	ALL b<a. f`b lepoll succ(m); y*y<=y;  \
\	(UN b<a.f`b)=y; Ord(a); m:nat; aa:f`b; b<a |]  \
\	==> (UN g<a++a. (lam g:a++a. if(g<a, vv2(f,b,g,aa),  \
\			ww2(f,b,THE l. l<a & g=a++l,aa)))`g) = y";
by (resolve_tac [UN_oadd RS ssubst] 1 THEN (atac 1));
by (resolve_tac [subst] 1 THEN (atac 1));
by (resolve_tac [UN_eq] 1);
by (forw_inst_tac [("i","a"),("k","ba")] lt_oadd1 1
	THEN (REPEAT (atac 1)));
by (forw_inst_tac [("j","a"),("k","ba")] oadd_lt_mono2 1
	THEN (REPEAT (atac 1)));
by (asm_simp_tac (ZF_ss addsimps [ltD RS beta,
	oadd_le_self RS le_imp_not_lt RS if_not_P, lt_Ord]) 1);
by (resolve_tac [the_only_b RS subst] 1 THEN (atac 1));
by (asm_simp_tac (ZF_ss 
	addsimps [vv2_subset RS subset_imp_Un_Diff_eq, ltI, ww2_def]) 1);
val UN_eq_y_2 = result();

(* ********************************************************************** *)
(* every value of defined function is less than or equipollent to m	  *)
(* ********************************************************************** *)

goalw thy [vv2_def]
	"!!m. [| m:nat; m~=0 |] ==> vv2(f,b,g,aa) lesspoll succ(m)";
by (resolve_tac [conjI RS (expand_if RS iffD2)] 1);
by (asm_simp_tac (AC_ss
	addsimps [empty_lepollI RS lepoll_imp_lesspoll_succ]) 2);
by (fast_tac (AC_cs
	addSDs [le_imp_subset RS subset_imp_lepoll RS lepoll_0_is_0]
	addSIs [singleton_eqpoll_1 RS eqpoll_imp_lepoll RS 
			lepoll_trans RS lepoll_imp_lesspoll_succ,
		not_lt_imp_le RS le_imp_subset RS subset_imp_lepoll,
		nat_into_Ord, nat_1I]) 1);
val vv2_lesspoll_succ = result();

goalw thy [ww2_def] "!!m. [| ALL b<a. f`b lepoll succ(m); g<a; m:nat;  \
\			vv2(f,b,g,d) <= f`g |]  \
\			==> ww2(f,b,g,d) lesspoll succ(m)";
by (excluded_middle_tac "f`g = 0" 1);
by (asm_simp_tac (AC_ss
		addsimps [empty_lepollI RS lepoll_imp_lesspoll_succ]) 2);
by (dresolve_tac [ospec] 1 THEN (atac 1));
by (resolve_tac [Diff_lepoll RS lepoll_imp_lesspoll_succ] 1
	THEN (TRYALL atac));
by (asm_simp_tac (AC_ss addsimps [vv2_def, expand_if, not_emptyI]) 1);
val ww2_lesspoll_succ = result();

goal thy "!!a. [| ALL g<a. ALL d<a. domain(uu(f,b,g,d)) ~= 0 -->  \
\		domain(uu(f,b,g,d)) eqpoll succ(m);  \
\		ALL b<a. f`b lepoll succ(m); y*y <= y;  \
\		(UN b<a. f`b)=y; b<a; aa:f`b; m:nat; m~= 0 |]  \
\		==> ALL ba<a++a. (lam g:a++a. if(g<a, vv2(f,b,g,aa),  \
\			ww2(f,b,THE l. l<a & g=a++l,aa)))`ba lepoll m";
by (resolve_tac [oallI] 1);
by (asm_full_simp_tac AC_ss 1);
by (resolve_tac [lesspoll_succ_imp_lepoll] 1 THEN (atac 2));
by (resolve_tac [conjI RS (expand_if RS iffD2)] 1);
by (asm_simp_tac (AC_ss addsimps [vv2_lesspoll_succ]) 1);
by (forward_tac [lt_oadd_disj1] 1 THEN (REPEAT (ares_tac [lt_Ord2] 1)));
by (fast_tac (FOL_cs addSIs [ww2_lesspoll_succ, vv2_subset]
		addSDs [theI]) 1);
val all_sum_lepoll_m_2 = result();

(* ********************************************************************** *)
(* lemma ii	 							  *)
(* ********************************************************************** *)
goalw thy [NN_def]
	"!!y. [| succ(m) : NN(y); y*y <= y; m:nat; m~=0 |] ==> m : NN(y)";
by (REPEAT (eresolve_tac [CollectE, exE, conjE] 1));
by (resolve_tac [quant_domain_uu_lepoll_m RS cases RS disjE] 1
    THEN (atac 1));
(* case 1 *)
by (resolve_tac [CollectI] 1);
by (atac 1);
by (res_inst_tac [("x","a ++ a")] exI 1);
by (res_inst_tac [("x","lam b:a++a. if (b<a, vv1(f,b,succ(m)),  \
\			ww1(f,THE l. l<a & b=a++l,succ(m)))")] exI 1);
by (fast_tac (FOL_cs addSIs [Ord_oadd, lam_funtype RS domain_of_fun,
				UN_eq_y, all_sum_lepoll_m]) 1);
(* case 2 *)
by (REPEAT (eresolve_tac [oexE, conjE] 1));
by (resolve_tac [CollectI] 1);
by (eresolve_tac [succ_natD] 1);
by (res_inst_tac [("A","f`?B")] not_emptyE 1 THEN (atac 1));
by (res_inst_tac [("x","a++a")] exI 1);
by (res_inst_tac [("x","lam g:a++a. if (g<a, vv2(f,b,g,x),  \
\			ww2(f,b,THE l. l<a & g=a++l,x))")] exI 1);
by (fast_tac (FOL_cs addSIs [Ord_oadd, lam_funtype RS domain_of_fun,
				UN_eq_y_2, all_sum_lepoll_m_2]) 1);
val lemma_ii = result();


(* ********************************************************************** *)
(* lemma iv - p. 4 :                                                      *)
(* For every set x there is a set y such that   x Un (y * y) <= y         *)
(* ********************************************************************** *)

(* the quantifier ALL looks inelegant but makes the proofs shorter  *)
(* (used only in the following two lemmas)                          *)

goal thy "ALL n:nat. rec(n, x, %k r. r Un r*r) <=  \
\                    rec(succ(n), x, %k r. r Un r*r)";
by (fast_tac (ZF_cs addIs [rec_succ RS ssubst]) 1);
val z_n_subset_z_succ_n = result();

goal thy "!!n. [| ALL n:nat. f(n)<=f(succ(n)); n le m; n : nat; m: nat |]  \
\              ==> f(n)<=f(m)";
by (res_inst_tac [("P","n le m")] impE 1 THEN (REPEAT (atac 2)));
by (res_inst_tac [("P","%z. n le z --> f(n) <= f(z)")] nat_induct 1);
by (REPEAT (fast_tac lt_cs 1));
val le_subsets = result();

goal thy "!!n m. [| n le m; m:nat |] ==>  \
\	rec(n, x, %k r. r Un r*r) <= rec(m, x, %k r. r Un r*r)";
by (resolve_tac [z_n_subset_z_succ_n RS le_subsets] 1 
    THEN (TRYALL atac));
by (eresolve_tac [Ord_nat RSN (2, ltI) RSN (2, lt_trans1) RS ltD] 1
    THEN (atac 1));
val le_imp_rec_subset = result();

goal thy "!!x. EX y. x Un y*y <= y";
by (res_inst_tac [("x","UN n:nat. rec(n, x, %k r. r Un r*r)")] exI 1);
by (resolve_tac [subsetI] 1);
by (eresolve_tac [UnE] 1);
by (resolve_tac [UN_I] 1);
by (eresolve_tac [rec_0 RS ssubst] 2);
by (resolve_tac [nat_0I] 1);
by (eresolve_tac [SigmaE] 1);
by (REPEAT (eresolve_tac [UN_E] 1));
by (res_inst_tac [("a","succ(n Un na)")] UN_I 1);
by (eresolve_tac [Un_nat_type RS nat_succI] 1 THEN (atac 1));
by (resolve_tac [rec_succ RS ssubst] 1);
by (fast_tac (ZF_cs addIs [le_imp_rec_subset RS subsetD]
		addSIs [Un_upper1_le, Un_upper2_le, Un_nat_type]
		addSEs [nat_into_Ord]) 1);
val lemma_iv = result();

(* ********************************************************************** *)
(* Rubin & Rubin wrote :						  *)
(* "It follows from (ii) and mathematical induction that if y*y <= y then *)
(* y can be well-ordered"						  *)

(* In fact we have to prove :						  *)
(*	* WO6 ==> NN(y) ~= 0						  *)
(*	* reverse induction which lets us infer that 1 : NN(y)		  *)
(*	* 1 : NN(y) ==> y can be well-ordered				  *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(*	WO6 ==> NN(y) ~= 0						  *)
(* ********************************************************************** *)

goalw thy [WO6_def, NN_def] "!!y. WO6 ==> NN(y) ~= 0";
by (eresolve_tac [allE] 1);
by (fast_tac (ZF_cs addSIs [not_emptyI]) 1);
val WO6_imp_NN_not_empty = result();

(* ********************************************************************** *)
(*	1 : NN(y) ==> y can be well-ordered				  *)
(* ********************************************************************** *)

goal thy "!!f. [| (UN b<a. f`b)=y; x:y; ALL b<a. f`b lepoll 1; Ord(a) |]  \
\		==> EX c<a. f`c = {x}";
by (fast_tac (AC_cs addSEs [lepoll_1_is_sing]) 1);
val lemma1 = result();

goal thy "!!f. [| (UN b<a. f`b)=y; x:y; ALL b<a. f`b lepoll 1; Ord(a) |]  \
\		==> f` (LEAST i. f`i = {x}) = {x}";
by (dresolve_tac [lemma1] 1 THEN (REPEAT (atac 1)));
by (fast_tac (AC_cs addSEs [lt_Ord] addIs [LeastI]) 1);
val lemma2 = result();

goalw thy [NN_def] "!!y. 1 : NN(y) ==> EX a f. Ord(a) & f:inj(y, a)";
by (eresolve_tac [CollectE] 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (res_inst_tac [("x","a")] exI 1);
by (res_inst_tac [("x","lam x:y. LEAST i. f`i = {x}")] exI 1);
by (resolve_tac [conjI] 1 THEN (atac 1));
by (res_inst_tac [("d","%i. THE x. x:f`i")] lam_injective 1);
by (dresolve_tac [lemma1] 1 THEN (REPEAT (atac 1)));
by (fast_tac (AC_cs addSEs [Least_le RS lt_trans1 RS ltD, lt_Ord]) 1);
by (resolve_tac [lemma2 RS ssubst] 1 THEN (REPEAT (atac 1)));
by (fast_tac (ZF_cs addSIs [the_equality]) 1);
val NN_imp_ex_inj = result();

goal thy "!!y. [| y*y <= y; 1 : NN(y) |] ==> EX r. well_ord(y, r)";
by (dresolve_tac [NN_imp_ex_inj] 1);
by (fast_tac (ZF_cs addSEs [well_ord_Memrel RSN (2,  well_ord_rvimage)]) 1);
val y_well_ord = result();

(* ********************************************************************** *)
(*	reverse induction which lets us infer that 1 : NN(y)		  *)
(* ********************************************************************** *)

val [prem1, prem2] = goal thy
	"[| n:nat; !!m. [| m:nat; m~=0; P(succ(m)) |] ==> P(m) |]  \
\	==> n~=0 --> P(n) --> P(1)";
by (res_inst_tac [("n","n")] nat_induct 1);
by (resolve_tac [prem1] 1);
by (fast_tac ZF_cs 1);
by (excluded_middle_tac "x=0" 1);
by (fast_tac ZF_cs 2);
by (fast_tac (ZF_cs addSIs [prem2]) 1);
val rev_induct_lemma = result();

val prems = goal thy
	"[| P(n); n:nat; n~=0;  \
\	!!m. [| m:nat; m~=0; P(succ(m)) |] ==> P(m) |]  \
\	==> P(1)";
by (resolve_tac [rev_induct_lemma RS impE] 1);
by (eresolve_tac [impE] 4 THEN (atac 5));
by (REPEAT (ares_tac prems 1));
val rev_induct = result();

goalw thy [NN_def] "!!n. n:NN(y) ==> n:nat";
by (fast_tac ZF_cs 1);
val NN_into_nat = result();

goal thy "!!n. [| n:NN(y); y*y <= y; n~=0 |] ==> 1:NN(y)";
by (resolve_tac [rev_induct] 1 THEN (REPEAT (ares_tac [NN_into_nat] 1)));
by (resolve_tac [lemma_ii] 1 THEN (REPEAT (atac 1)));
val lemma3 = result();

(* ********************************************************************** *)
(* Main theorem "WO6 ==> WO1"						  *)
(* ********************************************************************** *)

(* another helpful lemma *)
goalw thy [NN_def] "!!y. 0:NN(y) ==> y=0";
by (fast_tac (AC_cs addSIs [equalityI] 
                    addSDs [lepoll_0_is_0] addEs [subst]) 1);
val NN_y_0 = result();

goalw thy [WO1_def] "!!Z. WO6 ==> WO1";
by (resolve_tac [allI] 1);
by (excluded_middle_tac "A=0" 1);
by (fast_tac (ZF_cs addSIs [well_ord_Memrel, nat_0I RS nat_into_Ord]) 2);
by (res_inst_tac [("x1","A")] (lemma_iv RS revcut_rl) 1);
by (eresolve_tac [exE] 1);
by (dresolve_tac [WO6_imp_NN_not_empty] 1);
by (eresolve_tac [Un_subset_iff RS iffD1 RS conjE] 1);
by (eres_inst_tac [("A","NN(y)")] not_emptyE 1);
by (forward_tac [y_well_ord] 1);
by (fast_tac (ZF_cs addEs [well_ord_subset]) 2);
by (fast_tac (ZF_cs addSIs [lemma3] addSDs [NN_y_0] addSEs [not_emptyE]) 1);
qed "WO6_imp_WO1";

