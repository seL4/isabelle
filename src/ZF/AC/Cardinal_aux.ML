(*  Title:      ZF/AC/Cardinal_aux.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Auxiliary lemmas concerning cardinalities
*)

open Cardinal_aux;

(* ********************************************************************** *)
(* Lemmas involving ordinals and cardinalities used in the proofs         *)
(* concerning AC16 and DC                                                 *)
(* ********************************************************************** *)

(* j=|A| *)
goal Cardinal.thy
    "!!A. [| A lepoll i; Ord(i) |] ==> EX j. j le i & A eqpoll j";
by (fast_tac (!claset addIs [lepoll_cardinal_le, well_ord_Memrel,
                            well_ord_cardinal_eqpoll RS eqpoll_sym]
                    addDs [lepoll_well_ord]) 1);
qed "lepoll_imp_ex_le_eqpoll";

(* j=|A| *)
goalw Cardinal.thy [lesspoll_def]
    "!!A a. [| A lesspoll i; Ord(i) |] ==> EX j. j<i & A eqpoll j";
by (fast_tac (!claset addSDs [lepoll_imp_ex_le_eqpoll] addSEs [leE]) 1);
qed "lesspoll_imp_ex_lt_eqpoll";

goalw thy [InfCard_def] "!!i. [| ~Finite(i); Ord(i) |] ==> InfCard(|i|)";
by (rtac conjI 1);
by (rtac Card_cardinal 1);
by (resolve_tac [Card_nat RS (Card_def RS def_imp_iff RS iffD1 RS ssubst)] 1);
by (resolve_tac [nat_le_infinite_Ord RS le_imp_lepoll
        RSN (2, well_ord_Memrel RS well_ord_lepoll_imp_Card_le)] 1 
    THEN REPEAT (assume_tac 1));
qed "Inf_Ord_imp_InfCard_cardinal";

val sum_lepoll_prod = [sum_eq_2_times RS equalityD1 RS subset_imp_lepoll,
        asm_rl, lepoll_refl] MRS (prod_lepoll_mono RSN (2, lepoll_trans))
        |> standard;

goal thy "!!A. [| A lepoll B; 2 lepoll A |] ==> A+B lepoll A*B";
by (REPEAT (ares_tac [[sum_lepoll_mono, sum_lepoll_prod]
                MRS lepoll_trans, lepoll_refl] 1));
qed "lepoll_imp_sum_lepoll_prod";

goal thy "!!A. [| A eqpoll i; B eqpoll i; ~Finite(i); Ord(i) |]  \
\               ==> A Un B eqpoll i";
by (rtac eqpollI 1);
by (eresolve_tac [subset_imp_lepoll RSN (2, eqpoll_sym RS eqpoll_imp_lepoll
        RS  lepoll_trans)] 2);
by (Fast_tac 2);
by (resolve_tac [Un_lepoll_sum RS lepoll_trans] 1);
by (resolve_tac [lepoll_imp_sum_lepoll_prod RS lepoll_trans] 1);
by (eresolve_tac [eqpoll_sym RSN (2, eqpoll_trans) RS eqpoll_imp_lepoll] 1
        THEN (assume_tac 1));
by (resolve_tac [nat_le_infinite_Ord RS le_imp_lepoll RS 
        (Ord_nat RS (nat_2I RS OrdmemD) RS subset_imp_lepoll RS lepoll_trans)
        RS (eqpoll_sym RS eqpoll_imp_lepoll RSN (2, lepoll_trans))] 1 
    THEN (REPEAT (assume_tac 1)));
by (eresolve_tac [prod_eqpoll_cong RS eqpoll_imp_lepoll RS lepoll_trans] 1 
    THEN (assume_tac 1));
by (resolve_tac [Inf_Ord_imp_InfCard_cardinal RSN (2, well_ord_Memrel RS 
        well_ord_InfCard_square_eq) RS eqpoll_imp_lepoll] 1 
    THEN REPEAT (assume_tac 1));
qed "Un_eqpoll_Inf_Ord";

val ss = (!simpset) addsimps [inj_is_fun RS apply_type, left_inverse] 
               setloop (split_tac [expand_if] ORELSE' etac UnE);

goal ZF.thy "{x, y} - {y} = {x} - {y}";
by (Fast_tac 1);
qed "double_Diff_sing";

goal ZF.thy "if({y,z}-{z}=0, z, THE w. {y,z}-{z}={w}) = y";
by (split_tac [expand_if] 1);
by (asm_full_simp_tac (!simpset addsimps [double_Diff_sing, Diff_eq_0_iff]) 1);
by (fast_tac (!claset addSIs [the_equality] addEs [equalityE]) 1);
qed "paired_bij_lemma";

goal thy "(lam y:{{y,z}. y:x}. if(y-{z}=0, z, THE w. y-{z}={w}))  \
\               : bij({{y,z}. y:x}, x)";
by (res_inst_tac [("d","%a. {a,z}")] lam_bijective 1);
by (TRYALL (fast_tac (!claset addSEs [RepFunE] addSIs [RepFunI] 
                addss (!simpset addsimps [paired_bij_lemma]))));
qed "paired_bij";

goalw thy [eqpoll_def] "{{y,z}. y:x} eqpoll x";
by (fast_tac (!claset addSIs [paired_bij]) 1);
qed "paired_eqpoll";

goal thy "!!A. EX B. B eqpoll A & B Int C = 0";
by (fast_tac (!claset addSIs [paired_eqpoll, equals0I] addEs [mem_asym]) 1);
qed "ex_eqpoll_disjoint";

goal thy "!!A. [| A lepoll i; B lepoll i; ~Finite(i); Ord(i) |]  \
\               ==> A Un B lepoll i";
by (res_inst_tac [("A1","i"), ("C1","i")] (ex_eqpoll_disjoint RS exE) 1);
by (etac conjE 1);
by (dresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RSN (2, lepoll_trans)] 1);
by (assume_tac 1);
by (resolve_tac [Un_lepoll_Un RS lepoll_trans] 1 THEN (REPEAT (assume_tac 1)));
by (eresolve_tac [eqpoll_refl RSN (2, Un_eqpoll_Inf_Ord) RS
        eqpoll_imp_lepoll] 1
        THEN (REPEAT (assume_tac 1)));
qed "Un_lepoll_Inf_Ord";

goal thy "!!P. [| P(i); i:j; Ord(j) |] ==> (LEAST i. P(i)) : j";
by (eresolve_tac [Least_le RS leE] 1);
by (etac Ord_in_Ord 1 THEN (assume_tac 1));
by (etac ltE 1);
by (fast_tac (!claset addDs [OrdmemD]) 1);
by (etac subst_elem 1 THEN (assume_tac 1));
qed "Least_in_Ord";

goal thy "!!x. [| well_ord(x,r); y<=x; y lepoll succ(n); n:nat |]  \
\       ==> y-{THE b. first(b,y,r)} lepoll n";
by (res_inst_tac [("Q","y=0")] (excluded_middle RS disjE) 1);
by (fast_tac (!claset addSIs [Diff_sing_lepoll, the_first_in]) 1);
by (res_inst_tac [("b","y-{THE b. first(b, y, r)}")] subst 1);
by (rtac empty_lepollI 2);
by (Fast_tac 1);
qed "Diff_first_lepoll";

goal thy "(UN x:X. P(x)) <= (UN x:X. P(x)-Q(x)) Un (UN x:X. Q(x))";
by (Fast_tac 1);
qed "UN_subset_split";

goalw thy [lepoll_def] "!!a. Ord(a) ==> (UN x:a. {P(x)}) lepoll a";
by (res_inst_tac [("x","lam z:(UN x:a. {P(x)}). (LEAST i. P(i)=z)")] exI 1);
by (res_inst_tac [("d","%z. P(z)")] lam_injective 1);
by (fast_tac (!claset addSIs [Least_in_Ord]) 1);
by (fast_tac (!claset addIs [LeastI] addSEs [Ord_in_Ord]) 1);
qed "UN_sing_lepoll";

goal thy "!!a T. [| well_ord(T, R); ~Finite(a); Ord(a); n:nat |] ==>  \
\       ALL f. (ALL b:a. f`b lepoll n & f`b <= T) --> (UN b:a. f`b) lepoll a";
by (etac nat_induct 1);
by (rtac allI 1);
by (rtac impI 1);
by (res_inst_tac [("b","UN b:a. f`b")] subst 1);
by (rtac empty_lepollI 2);
by (resolve_tac [equals0I RS sym] 1);
by (REPEAT (eresolve_tac [UN_E, allE] 1));
by (fast_tac (!claset addDs [lepoll_0_is_0 RS subst]) 1);
by (rtac allI 1);
by (rtac impI 1);
by (eres_inst_tac [("x","lam x:a. f`x - {THE b. first(b,f`x,R)}")] allE 1);
by (etac impE 1);
by (Asm_full_simp_tac 1);
by (fast_tac (!claset addSIs [Diff_first_lepoll]) 1);
by (Asm_full_simp_tac 1);
by (resolve_tac [UN_subset_split RS subset_imp_lepoll RS lepoll_trans] 1);
by (rtac Un_lepoll_Inf_Ord 1 THEN (REPEAT_FIRST assume_tac));
by (etac UN_sing_lepoll 1);
qed "UN_fun_lepoll_lemma";

goal thy "!!a f. [| ALL b:a. f`b lepoll n & f`b <= T; well_ord(T, R);  \
\       ~Finite(a); Ord(a); n:nat |] ==> (UN b:a. f`b) lepoll a";
by (eresolve_tac [UN_fun_lepoll_lemma RS allE] 1 THEN (REPEAT (assume_tac 1)));
by (Fast_tac 1);
qed "UN_fun_lepoll";

goal thy "!!a f. [| ALL b:a. F(b) lepoll n & F(b) <= T; well_ord(T, R);  \
\       ~Finite(a); Ord(a); n:nat |] ==> (UN b:a. F(b)) lepoll a";
by (rtac impE 1 THEN (assume_tac 3));
by (res_inst_tac [("f","lam b:a. F(b)")] (UN_fun_lepoll) 2 
        THEN (TRYALL assume_tac));
by (Simp_tac 2);
by (Asm_full_simp_tac 1);
qed "UN_lepoll";

goal thy "!!a. Ord(a) ==> (UN b:a. F(b)) = (UN b:a. F(b) - (UN c:b. F(c)))";
by (rtac equalityI 1);
by (Fast_tac 2);
by (rtac subsetI 1);
by (etac UN_E 1);
by (rtac UN_I 1);
by (res_inst_tac [("P","%z. x:F(z)")] Least_in_Ord 1 THEN (REPEAT (assume_tac 1)));
by (rtac DiffI 1);
by (resolve_tac [Ord_in_Ord RSN (2, LeastI)] 1 THEN (REPEAT (assume_tac 1)));
by (rtac notI 1);
by (etac UN_E 1);
by (eres_inst_tac [("P","%z. x:F(z)"),("i","c")] less_LeastE 1);
by (eresolve_tac [Ord_Least RSN (2, ltI)] 1);
qed "UN_eq_UN_Diffs";

goalw thy [eqpoll_def] "!!A B. A Int B = 0 ==> A Un B eqpoll A + B";
by (res_inst_tac [("x","lam a:A Un B. if(a:A,Inl(a),Inr(a))")] exI 1);
by (res_inst_tac [("d","%z. case(%x.x, %x.x, z)")] lam_bijective 1);
by (fast_tac (!claset addSIs [if_type, InlI, InrI]) 1);
by (TRYALL (etac sumE ));
by (TRYALL (split_tac [expand_if]));
by (TRYALL Asm_simp_tac);
by (fast_tac (!claset addDs [equals0D]) 1);
qed "disj_Un_eqpoll_sum";

goalw thy [lepoll_def, eqpoll_def]
        "!!X a. a lepoll X ==> EX Y. Y<=X & a eqpoll Y";
by (etac exE 1);
by (forward_tac [subset_refl RSN (2, restrict_bij)] 1);
by (res_inst_tac [("x","f``a")] exI 1);
by (fast_tac (!claset addSEs [inj_is_fun RS fun_is_rel RS image_subset]) 1);
qed "lepoll_imp_eqpoll_subset";

(* ********************************************************************** *)
(* Diff_lesspoll_eqpoll_Card                                              *)
(* ********************************************************************** *)

goal thy "!!A B. [| A eqpoll a; ~Finite(a); Card(a); B lesspoll a;  \
\               A-B lesspoll a |] ==> P";
by (REPEAT (eresolve_tac [lesspoll_imp_ex_lt_eqpoll RS exE,
        Card_is_Ord, conjE] 1));
by (forw_inst_tac [("j","xa")] (lt_Ord RS (lt_Ord RSN (2, Un_upper1_le))) 1
        THEN (assume_tac 1));
by (forw_inst_tac [("j","xa")] (lt_Ord RS (lt_Ord RSN (2, Un_upper2_le))) 1
        THEN (assume_tac 1));
by (dtac Un_least_lt 1 THEN (assume_tac 1));
by (dresolve_tac [le_imp_lepoll RSN
        (2, eqpoll_imp_lepoll RS lepoll_trans)] 1
        THEN (assume_tac 1));
by (dresolve_tac [le_imp_lepoll RSN
        (2, eqpoll_imp_lepoll RS lepoll_trans)] 1
        THEN (assume_tac 1));
by (res_inst_tac [("Q","Finite(x Un xa)")] (excluded_middle RS disjE) 1);
by (dresolve_tac [[lepoll_Finite, lepoll_Finite] MRS Finite_Un] 2
        THEN (REPEAT (assume_tac 2)));
by (dresolve_tac [subset_Un_Diff RS subset_imp_lepoll RS lepoll_Finite] 2);
by (fast_tac (!claset
        addDs [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_Finite]) 2);
by (dresolve_tac [ Un_lepoll_Inf_Ord] 1
        THEN (REPEAT (assume_tac 1)));
by (fast_tac (!claset addSEs [ltE, Ord_in_Ord]) 1);
by (dresolve_tac [subset_Un_Diff RS subset_imp_lepoll RS lepoll_trans RSN
        (3, lt_Card_imp_lesspoll RS lepoll_lesspoll_lesspoll)] 1
        THEN (TRYALL assume_tac));
by (fast_tac (!claset addSDs [lesspoll_def RS def_imp_iff RS iffD1]) 1);
qed "Diff_lesspoll_eqpoll_Card_lemma";

goal thy "!!A. [| A eqpoll a; ~Finite(a); Card(a); B lesspoll a |]  \
\       ==> A - B eqpoll a";
by (rtac swap 1 THEN (Fast_tac 1));
by (rtac Diff_lesspoll_eqpoll_Card_lemma 1 THEN (REPEAT (assume_tac 1)));
by (fast_tac (!claset addSIs [lesspoll_def RS def_imp_iff RS iffD2,
        subset_imp_lepoll RS (eqpoll_imp_lepoll RSN (2, lepoll_trans))]) 1);
qed "Diff_lesspoll_eqpoll_Card";

