(*  Title:      ZF/AC/AC16_WO4.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

  The proof of AC16(n, k) ==> WO4(n-k)
*)

(* ********************************************************************** *)
(* The case of finite set                                                 *)
(* ********************************************************************** *)

Goalw [Finite_def] "[| Finite(A); 0<m; m:nat |] ==>  \
\       EX a f. Ord(a) & domain(f) = a &  \
\               (UN b<a. f`b) = A & (ALL b<a. f`b lepoll m)";
by (etac bexE 1);
by (dresolve_tac [eqpoll_sym RS (eqpoll_def RS def_imp_iff RS iffD1)] 1);
by (etac exE 1);
by (res_inst_tac [("x","n")] exI 1);
by (res_inst_tac [("x","lam i:n. {f`i}")] exI 1);
by (Asm_full_simp_tac 1);
by (rewrite_goals_tac [bij_def, surj_def]);
by (fast_tac (claset() addSIs [ltI, nat_into_Ord, lam_funtype RS domain_of_fun,
        equalityI, singleton_eqpoll_1 RS eqpoll_imp_lepoll RS lepoll_trans,
        nat_1_lepoll_iff RS iffD2]
        addSEs [apply_type, ltE]) 1);
val lemma1 = result();

(* ********************************************************************** *)
(* The case of infinite set                                               *)
(* ********************************************************************** *)

(* well_ord(x,r) ==> well_ord({{y,z}. y:x}, Something(x,z))  **)
bind_thm ("well_ord_paired", (paired_bij RS bij_is_inj RS well_ord_rvimage));

Goal "[| A lepoll B; ~ A lepoll C |] ==> ~ B lepoll C";
by (fast_tac (claset() addEs [notE, lepoll_trans]) 1);
qed "lepoll_trans1";

(* ********************************************************************** *)
(* There exists a well ordered set y such that ...                        *)
(* ********************************************************************** *)

val lepoll_paired = paired_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll;

Goal "EX y R. well_ord(y,R) & x Int y = 0 & ~y lepoll z & ~Finite(y)";
by (res_inst_tac [("x","{{a,x}. a:nat Un Hartog(z)}")] exI 1);
by (resolve_tac [transfer thy Ord_nat RS well_ord_Memrel RS (Ord_Hartog RS
                well_ord_Memrel RSN (2, well_ord_Un)) RS exE] 1);
by (fast_tac 
    (claset() addSIs [Ord_Hartog, well_ord_Memrel, well_ord_paired,
		      HartogI RSN (2, lepoll_trans1),
		 subset_imp_lepoll RS (lepoll_paired RSN (2, lepoll_trans))]
              addSEs [nat_not_Finite RS notE] addEs [mem_asym]
	      addSDs [Un_upper1 RS subset_imp_lepoll RS lepoll_Finite,
		      lepoll_paired RS lepoll_Finite]) 1);
val lemma2 = result();

val [prem] = goal thy "~Finite(B) ==> ~Finite(A Un B)";
by (fast_tac (claset()
        addSIs [subset_imp_lepoll RS (prem RSN (2, lepoll_infinite))]) 1);
qed "infinite_Un";

(* ********************************************************************** *)
(* There is a v : s(u) such that k lepoll x Int y (in our case succ(k))    *)
(* The idea of the proof is the following :                               *)
(* Suppose not, i.e. every element of s(u) has exactly k-1 elements of y   *)
(* Thence y is less than or equipollent to {v:Pow(x). v eqpoll n#-k}      *)
(*   We have obtained this result in two steps :                          *)
(*   1. y is less than or equipollent to {v:s(u). a <= v}                  *)
(*      where a is certain k-2 element subset of y                        *)
(*   2. {v:s(u). a <= v} is less than or equipollent                       *)
(*      to {v:Pow(x). v eqpoll n-k}                                       *)
(* ********************************************************************** *)

(*Proof simplified by LCP*)
Goal "[| ~(EX x:A. f`x=y); f : inj(A, B); y:B |]  \
\     ==> (lam a:succ(A). if(a=A, y, f`a)) : inj(succ(A), B)";
by (res_inst_tac [("d","%z. if(z=y, A, converse(f)`z)")] lam_injective 1);
by (auto_tac (claset(), simpset() addsimps [inj_is_fun RS apply_type]));
qed "succ_not_lepoll_lemma";

Goalw [lepoll_def, eqpoll_def, bij_def, surj_def]
        "[| ~A eqpoll B; A lepoll B |] ==> succ(A) lepoll B";
by (fast_tac (claset() addSEs [succ_not_lepoll_lemma, inj_is_fun]) 1);
qed "succ_not_lepoll_imp_eqpoll";


(* ********************************************************************** *)
(* There is a k-2 element subset of y                                     *)
(* ********************************************************************** *)

Goalw [lepoll_def, eqpoll_def]
        "[| n:nat; nat lepoll X |] ==> EX Y. Y<=X & n eqpoll Y";
by (fast_tac (subset_cs addSDs [Ord_nat RSN (2, OrdmemD) RSN (2, restrict_inj)]
        addSEs [restrict_bij, inj_is_fun RS fun_is_rel RS image_subset]) 1);
qed "nat_lepoll_imp_ex_eqpoll_n";

val ordertype_eqpoll =
        ordermap_bij RS (exI RS (eqpoll_def RS def_imp_iff RS iffD2));

Goalw [lesspoll_def] "n: nat ==> n lesspoll nat";
by (fast_tac (claset() addSEs [Ord_nat RSN (2, ltI) RS leI RS le_imp_lepoll,
			       eqpoll_sym RS eqpoll_imp_lepoll]
	      addIs [Ord_nat RSN (2, nat_succI RS ltI) RS leI
		     RS le_imp_lepoll RS lepoll_trans RS succ_lepoll_natE]) 1);
qed "n_lesspoll_nat";

Goal "[| a<=y; b:y-a; u:x |] ==> cons(b, cons(u, a)) : Pow(x Un y)";
by (Fast_tac 1);
qed "cons_cons_subset";

Goal "[| a eqpoll k; a<=y; b:y-a; u:x; x Int y = 0  \
\       |] ==> cons(b, cons(u, a)) eqpoll succ(succ(k))";
by (fast_tac (claset() addSIs [cons_eqpoll_succ]) 1);
qed "cons_cons_eqpoll";

Goal "[| succ(k) eqpoll A; k eqpoll B; B <= A; a : A-B; k:nat  \
\       |] ==> A = cons(a, B)";
by (rtac equalityI 1);
by (Fast_tac 2);
by (resolve_tac [Diff_eq_0_iff RS iffD1] 1);
by (rtac equals0I 1);
by (dresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll] 1);
by (dresolve_tac [eqpoll_sym RS cons_eqpoll_succ] 1);
by (Fast_tac 1);
by (dtac cons_eqpoll_succ 1);
by (Fast_tac 1);
by (fast_tac 
    (claset() 
        addSEs [[eqpoll_sym RS eqpoll_imp_lepoll, subset_imp_lepoll] MRS
        (lepoll_trans RS lepoll_trans) RS succ_lepoll_natE]) 1);
qed "set_eq_cons";

Goal "[| cons(x,a) = cons(y,a); x~: a |] ==> x = y ";
by (fast_tac (claset() addSEs [equalityE]) 1);
qed "cons_eqE";

Goal "A = B ==> A Int C = B Int C";
by (Asm_simp_tac 1);
qed "eq_imp_Int_eq";

(* ********************************************************************** *)
(* some arithmetic                                                        *)
(* ********************************************************************** *)

Goal "[| k:nat; m:nat |] ==>  \
\       ALL A B. A eqpoll k #+ m & k lepoll B & B<=A --> A-B lepoll m";
by (induct_tac "k" 1);
by (simp_tac (simpset() addsimps [add_0]) 1);
by (fast_tac (claset() addIs [eqpoll_imp_lepoll RS
        (Diff_subset RS subset_imp_lepoll RS lepoll_trans)]) 1);
by (REPEAT (resolve_tac [allI,impI] 1));
by (resolve_tac [succ_lepoll_imp_not_empty RS not_emptyE] 1);
by (Fast_tac 1);
by (eres_inst_tac [("x","A - {xa}")] allE 1);
by (eres_inst_tac [("x","B - {xa}")] allE 1);
by (etac impE 1);
by (asm_full_simp_tac (simpset() addsimps [add_succ]) 1);
by (fast_tac (claset() addSIs [Diff_sing_eqpoll, lepoll_Diff_sing]) 1);
by (res_inst_tac [("P","%z. z lepoll m")] subst 1 THEN (assume_tac 2));
by (Fast_tac 1);
qed "eqpoll_sum_imp_Diff_lepoll_lemma";

Goal "[| A eqpoll succ(k #+ m); B<=A; succ(k) lepoll B;  k:nat; m:nat |]  \
\     ==> A-B lepoll m";
by (dresolve_tac [add_succ RS ssubst] 1);
by (dresolve_tac [nat_succI RS eqpoll_sum_imp_Diff_lepoll_lemma] 1
        THEN (REPEAT (assume_tac 1)));
by (Fast_tac 1);
qed "eqpoll_sum_imp_Diff_lepoll";

(* ********************************************************************** *)
(* similar properties for eqpoll                                          *)
(* ********************************************************************** *)

Goal "[| k:nat; m:nat |] ==>  \
\       ALL A B. A eqpoll k #+ m & k eqpoll B & B<=A --> A-B eqpoll m";
by (induct_tac "k" 1);
by (fast_tac (claset() addSDs [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_0_is_0]
        addss (simpset() addsimps [add_0])) 1);
by (REPEAT (resolve_tac [allI,impI] 1));
by (resolve_tac [succ_lepoll_imp_not_empty RS not_emptyE] 1);
by (fast_tac (claset() addSEs [eqpoll_imp_lepoll]) 1);
by (eres_inst_tac [("x","A - {xa}")] allE 1);
by (eres_inst_tac [("x","B - {xa}")] allE 1);
by (etac impE 1);
by (fast_tac (claset() addSIs [Diff_sing_eqpoll,
        eqpoll_sym RSN (2, Diff_sing_eqpoll) RS eqpoll_sym]
        addss (simpset() addsimps [add_succ])) 1);
by (res_inst_tac [("P","%z. z eqpoll m")] subst 1 THEN (assume_tac 2));
by (Fast_tac 1);
qed "eqpoll_sum_imp_Diff_eqpoll_lemma";

Goal "[| A eqpoll succ(k #+ m); B<=A; succ(k) eqpoll B; k:nat; m:nat |]  \
\     ==> A-B eqpoll m";
by (dresolve_tac [add_succ RS ssubst] 1);
by (dresolve_tac [nat_succI RS eqpoll_sum_imp_Diff_eqpoll_lemma] 1
        THEN (REPEAT (assume_tac 1)));
by (Fast_tac 1);
qed "eqpoll_sum_imp_Diff_eqpoll";


(* ********************************************************************** *)
(* LL can be well ordered                                                 *)
(* ********************************************************************** *)

Goal "{x:Pow(X). x lepoll 0} = {0}";
by (fast_tac (claset() addSDs [lepoll_0_is_0] addSIs [lepoll_refl]) 1);
qed "subsets_lepoll_0_eq_unit";

Goal "n:nat ==> {z:Pow(y). z lepoll succ(n)} =  \
\               {z:Pow(y). z lepoll n} Un {z:Pow(y). z eqpoll succ(n)}";
by (fast_tac (claset() addIs [le_refl, leI, le_imp_lepoll]
                addSDs [lepoll_succ_disj]
                addSEs [nat_into_Ord, lepoll_trans, eqpoll_imp_lepoll]) 1);
qed "subsets_lepoll_succ";

Goal "n:nat ==> {z:Pow(y). z lepoll n} Int {z:Pow(y). z eqpoll succ(n)} = 0";
by (fast_tac (claset() addSEs [eqpoll_sym RS eqpoll_imp_lepoll 
                RS lepoll_trans RS succ_lepoll_natE]
                addSIs [equals0I]) 1);
qed "Int_empty";


Open_locale "AC16"; 

val all_ex = thm "all_ex";
val disjoint = thm "disjoint";
val includes = thm "includes";
val WO_R = thm "WO_R";
val k_def = thm "k_def";
val lnat = thm "lnat";
val mnat = thm "mnat";
val mpos = thm "mpos";
val Infinite = thm "Infinite";
val noLepoll = thm "noLepoll";

val LL_def = thm "LL_def";
val MM_def = thm "MM_def";
val GG_def = thm "GG_def";
val s_def = thm "s_def";

Addsimps [disjoint, WO_R, lnat, mnat, mpos, Infinite];
AddSIs [disjoint, WO_R, lnat, mnat, mpos];

Goalw [k_def] "k: nat";
by Auto_tac;
qed "knat";
Addsimps [knat];  AddSIs [knat];

AddSIs [Infinite];   (*if notI is removed!*)
AddSEs [Infinite RS notE];

AddEs [[disjoint, IntI] MRS (equals0D RS notE)];

(*use k = succ(l) *)
val includes_l = simplify (FOL_ss addsimps [k_def]) includes;
val all_ex_l = simplify (FOL_ss addsimps [k_def]) all_ex;

(* ********************************************************************** *)
(*   1. y is less than or equipollent to {v:s(u). a <= v}                  *)
(*      where a is certain k-2 element subset of y                        *)
(* ********************************************************************** *)

Goal "[| l eqpoll a; a <= y |] ==> y - a eqpoll y";
by (cut_facts_tac [WO_R, Infinite, lnat] 1);
by (fast_tac (empty_cs addIs [lepoll_lesspoll_lesspoll]
        addSIs [Card_cardinal, Diff_lesspoll_eqpoll_Card RS eqpoll_trans,
                Card_cardinal RS Card_is_Ord RS nat_le_infinite_Ord
                RS le_imp_lepoll]
        addSEs [well_ord_cardinal_eqpoll,
                well_ord_cardinal_eqpoll RS eqpoll_sym,
                eqpoll_sym RS eqpoll_imp_lepoll,
                n_lesspoll_nat RS lesspoll_lepoll_lesspoll,
                well_ord_cardinal_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll
                RS lepoll_infinite]) 1);
qed "Diff_Finite_eqpoll";

Goalw [s_def] "s(u) <= t_n";
by (Fast_tac 1);
qed "s_subset";

Goalw [s_def, succ_def, k_def]
      "[| w:t_n; cons(b,cons(u,a)) <= w; a <= y; b : y-a; l eqpoll a  \
\      |] ==> w: s(u)";
by (fast_tac (claset() addDs [eqpoll_imp_lepoll RS cons_lepoll_cong]
                addSEs [subset_imp_lepoll RSN (2, lepoll_trans)]) 1);
qed "sI";

Goalw [s_def] "v : s(u) ==> u : v";
by (Fast_tac 1);
qed "in_s_imp_u_in";


Goal "[| l eqpoll a;  a <= y;  b : y - a;  u : x |]  \
\     ==> EX! c. c: s(u) & a <= c & b:c";
by (rtac (all_ex_l RS ballE) 1);
by (blast_tac (claset() delrules [PowI]
		        addSIs [cons_cons_subset,
				eqpoll_sym RS cons_cons_eqpoll]) 2);
by (etac ex1E 1);
by (res_inst_tac [("a","w")] ex1I 1);
by (blast_tac (claset() addIs [sI]) 1);
by (etac allE 1);
by (etac impE 1);
by (assume_tac 2);
by (fast_tac (claset() addSEs [s_subset RS subsetD, in_s_imp_u_in]) 1);
qed "ex1_superset_a";

Goal "[| ALL v:s(u). succ(l) eqpoll v Int y;  \
\        l eqpoll a;  a <= y;  b : y - a;  u : x |]   \
\     ==> (THE c. c: s(u) & a <= c & b:c)  \
\              Int y = cons(b, a)";
by (forward_tac [ex1_superset_a RS theI] 1 THEN REPEAT (assume_tac 1));
by (rtac set_eq_cons 1);
by (REPEAT (Fast_tac 1));
qed "the_eq_cons";

Goal "[| ALL v:s(u). succ(l) eqpoll v Int y;  \
\        l eqpoll a;  a <= y;  u:x |]  \
\     ==> y lepoll {v:s(u). a <= v}";
by (resolve_tac [Diff_Finite_eqpoll RS eqpoll_sym RS 
		 eqpoll_imp_lepoll RS lepoll_trans] 1
    THEN REPEAT (Fast_tac 1));
by (res_inst_tac 
     [("f3", "lam b:y-a. THE c. c: s(u) & a <= c & b:c")]
     (exI RS (lepoll_def RS def_imp_iff RS iffD2)) 1);
by (simp_tac (simpset() addsimps [inj_def]) 1);
by (rtac conjI 1);
by (rtac lam_type 1);
by (forward_tac [ex1_superset_a RS theI] 1 THEN REPEAT (Fast_tac 1));
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (rtac cons_eqE 1);
by (Fast_tac 2);
by (dres_inst_tac [("A","THE c. ?P(c)"), ("C","y")] eq_imp_Int_eq 1);
by (asm_full_simp_tac (simpset() addsimps [the_eq_cons]) 1);
qed "y_lepoll_subset_s";


(* ********************************************************************** *)
(* back to the second part                                                *)
(* ********************************************************************** *)

Goal "w <= x Un y ==> w Int (x - {u}) = w - cons(u, w Int y)";
by (Fast_tac 1);
qed "w_Int_eq_w_Diff";

Goal "[| w:{v:s(u). a <= v};  \
\        l eqpoll a;  u : x;  \
\        ALL v:s(u). succ(l) eqpoll v Int y  \
\     |] ==> w Int (x - {u}) eqpoll m";
by (etac CollectE 1);
by (stac w_Int_eq_w_Diff 1);
by (fast_tac (claset() addSDs [s_subset RS subsetD,
			       includes_l RS subsetD]) 1);
by (fast_tac (claset() addSDs [bspec]
        addDs [s_subset RS subsetD, includes_l RS subsetD]
        addSEs [eqpoll_sym RS cons_eqpoll_succ RS eqpoll_sym, in_s_imp_u_in]
        addSIs [eqpoll_sum_imp_Diff_eqpoll]) 1);
qed "w_Int_eqpoll_m";

(* ********************************************************************** *)
(*   2. {v:s(u). a <= v} is less than or equipollent                       *)
(*      to {v:Pow(x). v eqpoll n-k}                                       *)
(* ********************************************************************** *)

Goal "x eqpoll m ==> x ~= 0";
by (cut_facts_tac [mpos] 1);
by (fast_tac (claset() addSEs [zero_lt_natE]
		       addSDs [eqpoll_succ_imp_not_empty]) 1);
qed "eqpoll_m_not_empty";

Goal "[| z : xa Int (x - {u}); l eqpoll a; a <= y; u:x |]  \
\     ==> EX! w. w : t_n & cons(z, cons(u, a)) <= w";
by (rtac (all_ex RS bspec) 1);
by (rewtac k_def);
by (fast_tac (claset() addSIs [cons_eqpoll_succ] addEs [eqpoll_sym]) 1);
qed "cons_cons_in";

Goal "[| ALL v:s(u). succ(l) eqpoll v Int y;  \
\        a <= y; l eqpoll a; u : x |]  \
\     ==> {v:s(u). a <= v} lepoll {v:Pow(x). v eqpoll m}";
by (res_inst_tac [("f3","lam w:{v:s(u). a <= v}. w Int (x - {u})")] 
        (exI RS (lepoll_def RS def_imp_iff RS iffD2)) 1);
by (simp_tac (simpset() addsimps [inj_def]) 1);
by (rtac conjI 1);
by (rtac lam_type 1);
by (rtac CollectI 1);
by (Fast_tac 1);
by (rtac w_Int_eqpoll_m 1 THEN REPEAT (assume_tac 1));
by (REPEAT (resolve_tac [ballI, impI] 1));
(** LEVEL 8 **)
by (resolve_tac [w_Int_eqpoll_m RS eqpoll_m_not_empty RS not_emptyE] 1);
by (EVERY (map Blast_tac [4,3,2,1]));
by (dresolve_tac [equalityD1 RS subsetD] 1 THEN (assume_tac 1));
by (forward_tac [cons_cons_in] 1 THEN REPEAT (assume_tac 1));
by (etac ex1_two_eq 1);
by (REPEAT (blast_tac
	    (claset() addDs [s_subset RS subsetD, in_s_imp_u_in]) 1));
qed "subset_s_lepoll_w";


(* ********************************************************************** *)
(* well_ord_subsets_lepoll_n                                              *)
(* ********************************************************************** *)

Goal "n:nat ==> EX S. well_ord({z: Pow(y) . z eqpoll succ(n)}, S)";
by (resolve_tac [WO_R RS well_ord_infinite_subsets_eqpoll_X
		 RS (eqpoll_def RS def_imp_iff RS iffD1) RS exE] 1);
by (REPEAT (fast_tac (claset() addIs [bij_is_inj RS well_ord_rvimage]) 1));
qed "well_ord_subsets_eqpoll_n";

Goal "n:nat ==> EX R. well_ord({z:Pow(y). z lepoll n}, R)";
by (induct_tac "n" 1);
by (force_tac (claset() addSIs [well_ord_unit],
	       simpset() addsimps [subsets_lepoll_0_eq_unit]) 1);
by (etac exE 1);
by (resolve_tac [well_ord_subsets_eqpoll_n RS exE] 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [subsets_lepoll_succ]) 1);
by (dtac well_ord_radd 1 THEN (assume_tac 1));
by (eresolve_tac [Int_empty RS disj_Un_eqpoll_sum RS 
                (eqpoll_def RS def_imp_iff RS iffD1) RS exE] 1);
by (fast_tac (claset() addSEs [bij_is_inj RS well_ord_rvimage]) 1);
qed "well_ord_subsets_lepoll_n";


Goalw [LL_def, MM_def] "LL <= {z:Pow(y). z lepoll succ(k #+ m)}";
by (cut_facts_tac [includes] 1);
by (fast_tac (claset() addIs [subset_imp_lepoll 
			      RS (eqpoll_imp_lepoll
				  RSN (2, lepoll_trans))]) 1);
qed "LL_subset";

Goal "EX S. well_ord(LL,S)";
by (rtac (well_ord_subsets_lepoll_n RS exE) 1);
by (blast_tac (claset() addIs [LL_subset RSN (2, well_ord_subset)]) 2);
by Auto_tac;
qed "well_ord_LL";

(* ********************************************************************** *)
(* every element of LL is a contained in exactly one element of MM        *)
(* ********************************************************************** *)

Goalw [MM_def, LL_def] "v:LL ==> EX! w. w:MM & v<=w";
by Safe_tac;
by (Fast_tac 1);
by (resolve_tac [lepoll_imp_eqpoll_subset RS exE] 1 THEN (assume_tac 1));
by (res_inst_tac [("x","x")] (all_ex RS ballE) 1);
by (fast_tac (claset() addSEs [eqpoll_sym]) 2);
by (Blast_tac 1);
qed "unique_superset_in_MM";

val unique_superset1 = unique_superset_in_MM RS theI RS conjunct1;
val unique_superset2 = unique_superset_in_MM RS the_equality2;


(* ********************************************************************** *)
(* The function GG satisfies the conditions of WO4                        *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* The union of appropriate values is the whole x                         *)
(* ********************************************************************** *)

Goalw [LL_def] "w : MM ==> w Int y : LL";
by (Fast_tac 1);
qed "Int_in_LL";

Goalw [LL_def] 
     "v : LL ==> v = (THE x. x : MM & v <= x) Int y";
by (Clarify_tac 1);
by (stac unique_superset2 1);
by (auto_tac (claset(), simpset() addsimps [Int_in_LL]));
qed "in_LL_eq_Int";

Goal "v : LL ==> (THE x. x : MM & v <= x) <= x Un y";
by (dtac unique_superset1 1);
by (rewtac MM_def);
by (fast_tac (claset() addSDs [unique_superset1, includes RS subsetD]) 1);
qed "the_in_MM_subset";

Goalw [GG_def] "v : LL ==> GG ` v <= x";
by (forward_tac [the_in_MM_subset] 1);
by (forward_tac [in_LL_eq_Int] 1); 
by (force_tac (claset() addEs [equalityE], simpset()) 1);
qed "GG_subset";


Goal "n:nat ==> EX z. z<=y & n eqpoll z";
by (etac nat_lepoll_imp_ex_eqpoll_n 1);
by (resolve_tac [ordertype_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll
        RSN (2, lepoll_trans)] 1);
by (rtac WO_R 2);
by (fast_tac 
    (claset() delrules [notI]
              addSIs [nat_le_infinite_Ord RS le_imp_lepoll]
	      addIs [Ord_ordertype, 
		     ordertype_eqpoll RS eqpoll_imp_lepoll
		     RS lepoll_infinite]) 1);
qed "ex_subset_eqpoll_n";


Goal "u:x ==> EX v : s(u). succ(k) lepoll v Int y";
by (rtac ccontr 1);
by (subgoal_tac "ALL v:s(u). k eqpoll v Int y" 1);
by (full_simp_tac (simpset() addsimps [s_def]) 2);
by (blast_tac (claset() addIs [succ_not_lepoll_imp_eqpoll]) 2);
by (rewtac k_def);
by (cut_facts_tac [all_ex, includes, lnat] 1);
by (rtac (ex_subset_eqpoll_n RS exE) 1 THEN assume_tac 1);
by (rtac (noLepoll RS notE) 1);
by (blast_tac (claset() addIs
	   [[y_lepoll_subset_s, subset_s_lepoll_w] MRS lepoll_trans]) 1);
qed "exists_proper_in_s";

Goal "u:x ==> EX w:MM. u:w";
by (eresolve_tac [exists_proper_in_s RS bexE] 1);
by (rewrite_goals_tac [MM_def, s_def]);
by (Fast_tac 1);
qed "exists_in_MM";

Goal "u:x ==> EX w:LL. u:GG`w";
by (rtac (exists_in_MM RS bexE) 1);
by (assume_tac 1);
by (rtac bexI 1);
by (etac Int_in_LL 2);
by (rewtac GG_def);
by (asm_simp_tac (simpset() addsimps [Int_in_LL]) 1);
by (stac unique_superset2 1);
by (REPEAT (fast_tac (claset() addSEs [Int_in_LL]) 1));
qed "exists_in_LL";


Goal "well_ord(LL,S) ==>      \
\     (UN b<ordertype(LL,S). GG ` (converse(ordermap(LL,S)) ` b)) = x";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac OUN_E 1);
by (resolve_tac [GG_subset RS subsetD] 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [ordermap_bij RS bij_converse_bij RS
			       bij_is_fun RS apply_type, ltD]) 1);
by (rtac subsetI 1);
by (eresolve_tac [exists_in_LL RS bexE] 1);
by (force_tac (claset() addIs [Ord_ordertype RSN (2, ltI),
			       ordermap_type RS apply_type],
        simpset() addsimps [ordermap_bij RS bij_is_inj RS left_inverse]) 1);
qed "OUN_eq_x";

(* ********************************************************************** *)
(* Every element of the family is less than or equipollent to n-k (m)     *)
(* ********************************************************************** *)

Goalw [MM_def] "w : MM ==> w eqpoll succ(k #+ m)";
by (fast_tac (claset() addDs [includes RS subsetD]) 1);
qed "in_MM_eqpoll_n";

Goalw [LL_def, MM_def] "w : LL ==> succ(k) lepoll w";
by (Fast_tac 1);
qed "in_LL_eqpoll_n";

val in_LL = in_LL_eq_Int RS equalityD1 RS (Int_lower1 RSN (2, subset_trans));

Goalw [GG_def] 
      "well_ord(LL,S) ==>      \
\      ALL b<ordertype(LL,S). GG ` (converse(ordermap(LL,S)) ` b) lepoll m";
by (rtac oallI 1);
by (asm_simp_tac 
    (simpset() addsimps [ltD,
			 ordermap_bij RS bij_converse_bij RS
			 bij_is_fun RS apply_type]) 1);
by (cut_facts_tac [includes] 1);
by (rtac eqpoll_sum_imp_Diff_lepoll 1);
by (REPEAT
    (fast_tac (claset() delrules [subsetI]
		        addSDs [ltD]
			addSIs [eqpoll_sum_imp_Diff_lepoll, in_LL_eqpoll_n]
			addIs [unique_superset1 RS in_MM_eqpoll_n, in_LL,
			       ordermap_bij RS bij_converse_bij RS 
			       bij_is_fun RS apply_type]) 1 ));
qed "all_in_lepoll_m";


Goal "EX a f. Ord(a) & domain(f) = a &  \
\             (UN b<a. f ` b) = x & (ALL b<a. f ` b lepoll m)";
by (resolve_tac [well_ord_LL RS exE] 1 THEN REPEAT (assume_tac 1));
by (rename_tac "S" 1);
by (res_inst_tac [("x","ordertype(LL,S)")] exI 1);
by (res_inst_tac [("x",
        "lam b:ordertype(LL,S). GG ` (converse(ordermap(LL,S)) ` b)")] 
    exI 1);
by (Simp_tac 1);
by (REPEAT (ares_tac [conjI, lam_funtype RS domain_of_fun,
		      Ord_ordertype, 
		      all_in_lepoll_m, OUN_eq_x] 1));
qed "conclusion";

Close_locale "AC16";



(* ********************************************************************** *)
(* The main theorem AC16(n, k) ==> WO4(n-k)                               *)
(* ********************************************************************** *)

Goalw [AC16_def,WO4_def]
        "[| AC16(k #+ m, k); 0 < k; 0 < m; k:nat; m:nat |] ==> WO4(m)";
by (rtac allI 1);
by (case_tac "Finite(A)" 1);
by (rtac lemma1 1 THEN REPEAT (assume_tac 1));
by (cut_facts_tac [lemma2] 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (eres_inst_tac [("x","A Un y")] allE 1);
by (forward_tac [infinite_Un] 1 THEN (mp_tac 1));
by (etac zero_lt_natE 1); by (assume_tac 1);
by (Clarify_tac 1);
by (DEPTH_SOLVE (ares_tac [export conclusion] 1));
qed "AC16_WO4";
