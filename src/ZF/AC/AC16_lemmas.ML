(*  Title:      ZF/AC/AC16_lemmas.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Lemmas used in the proofs concerning AC16
*)

Goal "a~:A ==> cons(a,A)-{a}=A";
by (Fast_tac 1);
qed "cons_Diff_eq";

Goalw [lepoll_def] "1 lepoll X <-> (EX x. x:X)";
by (rtac iffI 1);
by (fast_tac (claset() addIs [inj_is_fun RS apply_type]) 1);
by (etac exE 1);
by (res_inst_tac [("x","lam a:1. x")] exI 1);
by (fast_tac (claset() addSIs [lam_injective]) 1);
qed "nat_1_lepoll_iff";

Goal "X eqpoll 1 <-> (EX x. X={x})";
by (rtac iffI 1);
by (etac eqpollE 1);
by (dresolve_tac [nat_1_lepoll_iff RS iffD1] 1);
by (fast_tac (claset() addSIs [lepoll_1_is_sing]) 1);
by (fast_tac (claset() addSIs [singleton_eqpoll_1]) 1);
qed "eqpoll_1_iff_singleton";

Goalw [succ_def] "[| x eqpoll n; y~:x |] ==> cons(y,x) eqpoll succ(n)";
by (fast_tac (claset() addSEs [cons_eqpoll_cong, mem_irrefl]) 1);
qed "cons_eqpoll_succ";

Goal "{Y:Pow(X). Y eqpoll 1} = {{x}. x:X}";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac CollectE 1);
by (dresolve_tac [eqpoll_1_iff_singleton RS iffD1] 1);
by (fast_tac (claset() addSIs [RepFunI]) 1);
by (rtac subsetI 1);
by (etac RepFunE 1);
by (rtac CollectI 1);
by (Fast_tac 1);
by (fast_tac (claset() addSIs [singleton_eqpoll_1]) 1);
qed "subsets_eqpoll_1_eq";

Goalw [eqpoll_def, bij_def] "X eqpoll {{x}. x:X}";
by (res_inst_tac [("x","lam x:X. {x}")] exI 1);
by (rtac IntI 1);
by (rewrite_goals_tac [inj_def, surj_def]);
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addSIs [lam_type, RepFunI] 
                addIs [singleton_eq_iff RS iffD1]) 1);
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addSIs [lam_type]) 1);
qed "eqpoll_RepFun_sing";

Goal "{Y:Pow(X). Y eqpoll 1} eqpoll X";
by (resolve_tac [subsets_eqpoll_1_eq RS ssubst] 1);
by (resolve_tac [eqpoll_RepFun_sing RS eqpoll_sym] 1);
qed "subsets_eqpoll_1_eqpoll";

Goal "[| InfCard(x); y:Pow(x); y eqpoll succ(z) |]  \
\               ==> (LEAST i. i:y) : y";
by (eresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RS 
                succ_lepoll_imp_not_empty RS not_emptyE] 1);
by (fast_tac (claset() addIs [LeastI]
        addSDs [InfCard_is_Card RS Card_is_Ord, PowD RS subsetD]
        addEs [Ord_in_Ord]) 1);
qed "InfCard_Least_in";

Goalw [lepoll_def] "[| InfCard(x); n:nat |] ==>  \
\       {y:Pow(x). y eqpoll succ(succ(n))} lepoll  \
\       x*{y:Pow(x). y eqpoll succ(n)}";
by (res_inst_tac [("x","lam y:{y:Pow(x). y eqpoll succ(succ(n))}. \
\               <LEAST i. i:y, y-{LEAST i. i:y}>")] exI 1);
by (res_inst_tac [("d","%z. cons(fst(z),snd(z))")] lam_injective 1);
by (rtac SigmaI 1);
by (etac CollectE 1);
by (Asm_full_simp_tac 3);
by (rtac equalityI 3);
by (Fast_tac 4);
by (rtac subsetI 3);
by (etac consE 3);
by (Fast_tac 4);
by (rtac CollectI 2);
by (Fast_tac 2);
by (resolve_tac [PowD RS subsetD] 1 THEN (assume_tac 1));
by (REPEAT (fast_tac (claset() addSIs [Diff_sing_eqpoll]
                addIs [InfCard_Least_in]) 1));
qed "subsets_lepoll_lemma1";

val prems = goal thy "(!!y. y:z ==> Ord(y)) ==> z <= succ(Union(z))";
by (rtac subsetI 1);
by (res_inst_tac [("Q","ALL y:z. y<=x")] (excluded_middle RS disjE) 1);
by (Fast_tac 2);
by (etac swap 1);
by (rtac ballI 1);
by (rtac Ord_linear_le 1);
by (dtac le_imp_subset 3 THEN (assume_tac 3));
by (fast_tac (claset() addDs prems) 1);
by (fast_tac (claset() addDs prems) 1);
by (fast_tac (claset() addSEs [leE,ltE]) 1);
qed "set_of_Ord_succ_Union";

Goal "j<=i ==> i ~: j";
by (fast_tac (claset() addSEs [mem_irrefl]) 1);
qed "subset_not_mem";

val prems = goal thy "(!!y. y:z ==> Ord(y)) ==> succ(Union(z)) ~: z";
by (resolve_tac [set_of_Ord_succ_Union RS subset_not_mem] 1);
by (eresolve_tac prems 1);
qed "succ_Union_not_mem";

Goal "Union(cons(succ(Union(z)),z)) = succ(Union(z))";
by (Fast_tac 1);
qed "Union_cons_eq_succ_Union";

Goal "[| Ord(i); Ord(j) |] ==> i Un j = i | i Un j = j";
by (fast_tac (claset() addSDs [le_imp_subset] addEs [Ord_linear_le]) 1);
qed "Un_Ord_disj";

Goal "x:X ==> Union(X) = x Un Union(X-{x})";
by (Fast_tac 1);
qed "Union_eq_Un";

Goal "n:nat ==>  \
\       ALL z. (ALL y:z. Ord(y)) & z eqpoll n & z~=0 --> Union(z) : z";
by (induct_tac "n" 1);
by (fast_tac (claset() addSDs [eqpoll_imp_lepoll RS lepoll_0_is_0]) 1);
by (REPEAT (resolve_tac [allI, impI] 1));
by (etac natE 1);
by (fast_tac (claset() addSDs [eqpoll_1_iff_singleton RS iffD1]
        addSIs [Union_singleton]) 1);
by (hyp_subst_tac 1);
by (REPEAT (eresolve_tac [conjE, not_emptyE] 1));
by (eres_inst_tac [("x","z-{xb}")] allE 1);
by (etac impE 1);
by (fast_tac (claset() addSEs [Diff_sing_eqpoll,
                Diff_sing_eqpoll RS eqpoll_succ_imp_not_empty]) 1);
by (resolve_tac [Union_eq_Un RSN (2, subst_elem)] 1 THEN (assume_tac 2));
by (ftac bspec 1 THEN (assume_tac 1));
by (dresolve_tac [Diff_subset RS subsetD RSN (2, bspec)] 1 THEN (assume_tac 1));
by (dtac Un_Ord_disj 1 THEN (assume_tac 1));
by (etac DiffE 1);
by (etac disjE 1);
by (etac subst_elem 1 THEN (assume_tac 1));
by (rtac subst_elem 1 THEN (TRYALL assume_tac));
qed "Union_in_lemma";

Goal "[| ALL x:z. Ord(x); z eqpoll n; z~=0; n:nat |]  \
\               ==> Union(z) : z";
by (dtac Union_in_lemma 1);
by (fast_tac FOL_cs 1);
qed "Union_in";

Goal "[| InfCard(x); z:Pow(x); z eqpoll n; n:nat |]  \
\               ==> succ(Union(z)) : x";
by (resolve_tac [Limit_has_succ RS ltE] 1 THEN (assume_tac 3));
by (etac InfCard_is_Limit 1);
by (excluded_middle_tac "z=0" 1);
by (fast_tac (claset() addSIs [InfCard_is_Limit RS Limit_has_0]
                      addss (simpset())) 2);
by (resolve_tac
        [PowD RS subsetD RS (InfCard_is_Card RS Card_is_Ord RSN (2, ltI))] 1
        THEN (TRYALL assume_tac));
by (fast_tac (claset() addSIs [Union_in]
                      addSEs [PowD RS subsetD RSN 
		 (2, InfCard_is_Card RS Card_is_Ord RS Ord_in_Ord)]) 1);
qed "succ_Union_in_x";

Goalw [lepoll_def] "[| InfCard(x); n:nat |] ==>  \
\       {y:Pow(x). y eqpoll succ(n)} lepoll  \
\       {y:Pow(x). y eqpoll succ(succ(n))}";
by (res_inst_tac [("x","lam z:{y:Pow(x). y eqpoll succ(n)}.  \
\       cons(succ(Union(z)), z)")] exI 1);
by (res_inst_tac [("d","%z. z-{Union(z)}")] lam_injective 1);
by (resolve_tac [Union_cons_eq_succ_Union RS ssubst] 2);
by (rtac cons_Diff_eq 2);
by (fast_tac (claset() addSDs [InfCard_is_Card RS Card_is_Ord]
        addEs [Ord_in_Ord] addSIs [succ_Union_not_mem]) 2);
by (rtac CollectI 1);
by (fast_tac (claset() addSEs [cons_eqpoll_succ] 
                    addSIs [succ_Union_not_mem] 
                    addSDs [InfCard_is_Card RS Card_is_Ord] 
                    addEs  [Ord_in_Ord]) 2);
by (fast_tac (claset() addSIs [succ_Union_in_x]) 1);
qed "succ_lepoll_succ_succ";

Goal "[| InfCard(X); n:nat |]  \
\       ==> {Y:Pow(X). Y eqpoll succ(n)} eqpoll X";
by (induct_tac "n" 1);
by (rtac subsets_eqpoll_1_eqpoll 1);
by (rtac eqpollI 1);
by (resolve_tac [subsets_lepoll_lemma1 RS lepoll_trans] 1 
        THEN (REPEAT (assume_tac 1)));
by (resolve_tac [InfCard_is_Card RS Card_is_Ord RS well_ord_Memrel RS
                well_ord_InfCard_square_eq RS eqpoll_imp_lepoll
                RSN (2, lepoll_trans)] 1 THEN (assume_tac 2));
by (resolve_tac [InfCard_is_Card RS Card_cardinal_eq RS ssubst] 2 
        THEN (REPEAT (assume_tac 2)));
by (eresolve_tac [eqpoll_refl RS prod_eqpoll_cong RS eqpoll_imp_lepoll] 1);
by (fast_tac (claset() addEs [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_trans]
        addSIs [succ_lepoll_succ_succ]) 1);
qed "subsets_eqpoll_X";

Goalw [surj_def] "[| f:surj(A,B); y<=B |]  \
\       ==> f``(converse(f)``y) = y";
by (fast_tac (claset() addDs [apply_equality2]
	              addEs [apply_iff RS iffD2]) 1);
qed "image_vimage_eq";

Goal "[| f:inj(A,B); y<=A |] ==> converse(f)``(f``y) = y";
by (fast_tac (claset() addSEs [inj_is_fun RS apply_Pair]
                addDs [inj_equality]) 1);
qed "vimage_image_eq";

Goalw [eqpoll_def] "A eqpoll B  \
\       ==> {Y:Pow(A). Y eqpoll n} eqpoll {Y:Pow(B). Y eqpoll n}";
by (etac exE 1);
by (res_inst_tac [("x","lam X:{Y:Pow(A). EX f. f : bij(Y, n)}. f``X")] exI 1);
by (res_inst_tac [("d","%Z. converse(f)``Z")] lam_bijective 1);
by (fast_tac (claset()
        addSIs [bij_is_inj RS restrict_bij RS bij_converse_bij RS comp_bij] 
        addSEs [bij_is_fun RS fun_is_rel RS image_subset RS PowI]) 1);
by (fast_tac (claset() addSIs [bij_converse_bij RS bij_is_inj RS restrict_bij
                        RS bij_converse_bij RS comp_bij] 
                    addSEs [bij_converse_bij RS bij_is_fun RS fun_is_rel
                        RS image_subset RS PowI]) 1);
by (fast_tac (claset() addSEs [bij_is_inj RS vimage_image_eq]) 1);
by (fast_tac (claset() addSEs [bij_is_surj RS image_vimage_eq]) 1);
qed "subsets_eqpoll";

Goalw [WO2_def] "WO2 ==> EX a. Card(a) & X eqpoll a";
by (REPEAT (eresolve_tac [allE,exE,conjE] 1));
by (fast_tac (claset() addSEs [well_ord_Memrel RS well_ord_cardinal_eqpoll RS
                (eqpoll_sym RSN (2, eqpoll_trans)) RS eqpoll_sym]
                addSIs [Card_cardinal]) 1);
qed "WO2_imp_ex_Card";

Goal "[| X lepoll Y; ~Finite(X) |] ==> ~Finite(Y)";
by (fast_tac (empty_cs addEs [notE, lepoll_Finite] addSIs [notI]) 1); 
qed "lepoll_infinite";

Goalw [InfCard_def] "[| ~Finite(X); Card(X) |] ==> InfCard(X)";
by (fast_tac (claset() addSEs [Card_is_Ord RS nat_le_infinite_Ord]) 1);
qed "infinite_Card_is_InfCard";

Goal "[| WO2; n:nat; ~Finite(X) |]  \
\       ==> {Y:Pow(X). Y eqpoll succ(n)} eqpoll X";
by (dtac WO2_imp_ex_Card 1);
by (REPEAT (eresolve_tac [allE,exE,conjE] 1));
by (forward_tac [eqpoll_imp_lepoll RS lepoll_infinite] 1 THEN (assume_tac 1));
by (dtac infinite_Card_is_InfCard 1 THEN (assume_tac 1));
by (resolve_tac [eqpoll_trans RS eqpoll_trans] 1);
by (etac subsets_eqpoll 1);
by (etac subsets_eqpoll_X 1 THEN (assume_tac 1));
by (etac eqpoll_sym 1);
qed "WO2_infinite_subsets_eqpoll_X";

Goal "well_ord(X,R) ==> EX a. Card(a) & X eqpoll a";
by (fast_tac (claset() addSEs [well_ord_cardinal_eqpoll RS eqpoll_sym]
                addSIs [Card_cardinal]) 1);
qed "well_ord_imp_ex_Card";

Goal "[| well_ord(X,R); n:nat; ~Finite(X) |]  \
\               ==> {Y:Pow(X). Y eqpoll succ(n)} eqpoll X";
by (dtac well_ord_imp_ex_Card 1);
by (REPEAT (eresolve_tac [allE,exE,conjE] 1));
by (forward_tac [eqpoll_imp_lepoll RS lepoll_infinite] 1 THEN (assume_tac 1));
by (dtac infinite_Card_is_InfCard 1 THEN (assume_tac 1));
by (resolve_tac [eqpoll_trans RS eqpoll_trans] 1);
by (etac subsets_eqpoll 1);
by (etac subsets_eqpoll_X 1 THEN (assume_tac 1));
by (etac eqpoll_sym 1);
qed "well_ord_infinite_subsets_eqpoll_X";

