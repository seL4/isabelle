(*  Title:      ZF/AC/DC.ML
    ID:  $Id$
    Author:     Krzysztof Grabczewski

The proofs concerning the Axiom of Dependent Choice
*)

open DC;

(* ********************************************************************** *)
(* DC ==> DC(omega)                                                       *)
(*                                                                        *)
(* The scheme of the proof:                                               *)
(*                                                                        *)
(* Assume DC. Let R and x satisfy the premise of DC(omega).               *)
(*                                                                        *)
(* Define XX and RR as follows:                                           *)
(*                                                                        *)
(*       XX = (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R})              *)
(*       f RR g iff domain(g)=succ(domain(f)) &                           *)
(*              restrict(g, domain(f)) = f                                *)
(*                                                                        *)
(* Then RR satisfies the hypotheses of DC.                                *)
(* So applying DC:                                                        *)
(*                                                                        *)
(*       EX f:nat->XX. ALL n:nat. f`n RR f`succ(n)                        *)
(*                                                                        *)
(* Thence                                                                 *)
(*                                                                        *)
(*       ff = {<n, f`succ(n)`n>. n:nat}                                   *)
(*                                                                        *)
(* is the desired function.                                               *)
(*                                                                        *)
(* ********************************************************************** *)

goal thy "{<z1,z2>:XX*XX. domain(z2)=succ(domain(z1))  \
\       & restrict(z2, domain(z1)) = z1} <= XX*XX";
by (Fast_tac 1);
val lemma1_1 = result();

goal thy "!!X. ALL Y:Pow(X). Y lesspoll nat --> (EX x:X. <Y, x> : R)  \
\       ==> {<z1,z2>: (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R}) *  \
\               (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R}).  \
\               domain(z2)=succ(domain(z1))  \
\               & restrict(z2, domain(z1)) = z1} ~= 0";
by (etac ballE 1);
by (eresolve_tac [empty_subsetI RS PowI RSN (2, notE)] 2);
by (eresolve_tac [nat_0I RS n_lesspoll_nat RSN (2, impE)] 1);
by (etac bexE 1);
by (res_inst_tac [("a","<0, {<0, x>}>")] not_emptyI 1);
by (rtac CollectI 1);
by (rtac SigmaI 1);
by (fast_tac (claset() addSIs [nat_0I RS UN_I, empty_fun]) 1);
by (rtac (nat_1I RS UN_I) 1);
by (fast_tac (claset() addSIs [singleton_fun RS Pi_type]
        addss (simpset() addsimps [singleton_0 RS sym])) 1);
by (asm_full_simp_tac (simpset() addsimps [domain_0, domain_cons,
                singleton_0]) 1);
val lemma1_2 = result();

goal thy "!!X. ALL Y:Pow(X). Y lesspoll nat --> (EX x:X. <Y, x> : R)  \
\       ==> range({<z1,z2>: (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R}) *  \
\               (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R}).  \
\               domain(z2)=succ(domain(z1))  \
\               & restrict(z2, domain(z1)) = z1})  \
\       <=  domain({<z1,z2>: (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R}) *  \
\               (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R}).  \
\               domain(z2)=succ(domain(z1))  \
\               & restrict(z2, domain(z1)) = z1})";
by (rtac range_subset_domain 1);
by (rtac subsetI 2);
by (etac CollectD1 2);
by (etac UN_E 1);
by (etac CollectE 1);
by (dresolve_tac [fun_is_rel RS image_subset RS PowI RSN (2, bspec)] 1
        THEN (assume_tac 1));
by (eresolve_tac [[n_lesspoll_nat, nat_into_Ord RSN (2, image_Ord_lepoll)]
        MRS lepoll_lesspoll_lesspoll RSN (2, impE)] 1
        THEN REPEAT (assume_tac 1));
by (etac bexE 1);
by (res_inst_tac [("x","cons(<n,x>, g)")] exI 1);
by (rtac CollectI 1);
by (rtac SigmaI 1);
by (Fast_tac 1);
by (rtac UN_I 1);
by (etac nat_succI 1);
by (rtac CollectI 1);
by (etac cons_fun_type2 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [succE] addss (simpset()
        addsimps [cons_image_n, cons_val_n, cons_image_k, cons_val_k])) 1);
by (asm_full_simp_tac (simpset()
        addsimps [domain_cons, domain_of_fun, succ_def, restrict_cons_eq]) 1);
val lemma1_3 = result();

goal thy "!!X. [| XX = (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R});  \
\       RR = {<z1,z2>:XX*XX. domain(z2)=succ(domain(z1))  \
\       & restrict(z2, domain(z1)) = z1};  \
\       ALL Y:Pow(X). Y lesspoll nat --> (EX x:X. <Y, x> : R)  \
\       |] ==> RR <= XX*XX & RR ~= 0 & range(RR) <= domain(RR)";
by (fast_tac (claset() addSIs [lemma1_1] addSEs [lemma1_2, lemma1_3]) 1);
val lemma1 = result();

goal thy
"!!X.[| XX = (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R});  \
\       ALL n:nat. <f`n, f`succ(n)> :  \
\       {<z1,z2>:XX*XX. domain(z2)=succ(domain(z1))  \
\                       & restrict(z2, domain(z1)) = z1};  \
\       f: nat -> XX; n:nat  \
\    |] ==> EX k:nat. f`succ(n) : k -> X & n:k  \
\              & <f`succ(n)``n, f`succ(n)`n> : R";
by (etac nat_induct 1);
by (dresolve_tac [nat_1I RSN (2, apply_type)] 1);
by (dresolve_tac [nat_0I RSN (2, bspec)] 1);
by (Asm_full_simp_tac 1);
by Safe_tac;
by (rtac bexI 1 THEN (assume_tac 2));
by (best_tac (claset() addIs [ltD]
                      addSEs [nat_0_le RS leE]
        addEs [sym RS trans RS succ_neq_0, domain_of_fun]
        addss (simpset())) 1);
(** LEVEL 7 **)
by (dresolve_tac [nat_succI RSN (2, bspec)] 1 THEN (assume_tac 1));
by (subgoal_tac "f ` succ(succ(x)) : succ(k)->X" 1);
by (dresolve_tac [nat_succI RS nat_succI RSN (2, apply_type)] 1
        THEN (assume_tac 1));
by (Full_simp_tac 1);
by Safe_tac;
by (forw_inst_tac [("a","succ(k)")] (domain_of_fun RS sym RS trans) 1 THEN
    (assume_tac 1));
by (forw_inst_tac [("a","xa")] (domain_of_fun RS sym RS trans) 1 THEN
    (assume_tac 1));
by (fast_tac (claset() addSEs [nat_succI, nat_into_Ord RS succ_in_succ]
        addSDs [nat_into_Ord RS succ_in_succ RSN (2, bspec)]) 1);
by (dtac domain_of_fun 1);
by (Full_simp_tac 1);
by (deepen_tac (claset() addDs [domain_of_fun RS sym RS trans]) 0 1);
val lemma2 = result();

goal thy 
"!!X.[| XX = (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R});  \
\       ALL n:nat. <f`n, f`succ(n)> :  \
\       {<z1,z2>:XX*XX. domain(z2)=succ(domain(z1))  \
\       & restrict(z2, domain(z1)) = z1};  \
\       f: nat -> XX; n:nat \
\    |] ==>  ALL x:n. f`succ(n)`x = f`succ(x)`x";
by (etac nat_induct 1);
by (Fast_tac 1);
by (rtac ballI 1);
by (etac succE 1);
by (rtac restrict_eq_imp_val_eq 1);
by (dresolve_tac [nat_succI RSN (2, bspec)] 1 THEN (assume_tac 1));
by (Asm_full_simp_tac 1);
by (dtac lemma2 1 THEN REPEAT (assume_tac 1));
by (fast_tac (claset() addSDs [domain_of_fun]) 1);
by (dres_inst_tac [("x","xa")] bspec 1 THEN (assume_tac 1));
by (eresolve_tac [sym RS trans RS sym] 1);
by (resolve_tac [restrict_eq_imp_val_eq RS sym] 1);
by (dresolve_tac [nat_succI RSN (2, bspec)] 1 THEN (assume_tac 1));
by (Asm_full_simp_tac 1);
by (dtac lemma2 1 THEN REPEAT (assume_tac 1));
by (fast_tac (FOL_cs addSDs [domain_of_fun]
        addSEs [bexE, nat_into_Ord RSN (2, OrdmemD) RS subsetD]) 1);
val lemma3_1 = result();

goal thy "!!n. ALL x:n. f`succ(n)`x = f`succ(x)`x   \
\       ==> {f`succ(x)`x. x:n} = {f`succ(n)`x. x:n}";
by (Asm_full_simp_tac 1);
val lemma3_2 = result();

goal thy "!!X. [| XX = (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R});  \
\       ALL n:nat. <f`n, f`succ(n)> :  \
\       {<z1,z2>:XX*XX. domain(z2)=succ(domain(z1))  \
\       & restrict(z2, domain(z1)) = z1};  \
\       f: nat -> XX; n:nat  \
\       |] ==> (lam x:nat. f`succ(x)`x) `` n = f`succ(n)``n";
by (etac natE 1);
by (asm_full_simp_tac (simpset() addsimps [image_0]) 1);
by (resolve_tac [image_lam RS ssubst] 1);
by (fast_tac (claset() addSEs [[nat_succI, Ord_nat] MRS OrdmemD]) 1);
by (resolve_tac [lemma3_1 RS lemma3_2 RS ssubst] 1
        THEN REPEAT (assume_tac 1));
by (fast_tac (claset() addSEs [nat_succI]) 1);
by (dresolve_tac [nat_succI RSN (4, lemma2)] 1
        THEN REPEAT (assume_tac 1));
by (fast_tac (claset() addSEs [nat_into_Ord RSN (2, OrdmemD) RSN 
                            (2, image_fun RS sym)]) 1);
val lemma3 = result();

goal thy "!!f. [| f:A->B; B<=C |] ==> f:A->C";
by (rtac Pi_type 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [apply_type]) 1);
qed "fun_type_gen";

goalw thy [DC_def, DC0_def] "!!Z. DC0 ==> DC(nat)";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [conjE, allE] 1));
by (eresolve_tac [[refl, refl] MRS lemma1 RSN (2, impE)] 1
        THEN (assume_tac 1));
by (etac bexE 1);
by (res_inst_tac [("x","lam n:nat. f`succ(n)`n")] bexI 1);
by (fast_tac (claset() addSIs [lam_type] addSDs [refl RS lemma2]
                addSEs [fun_type_gen, apply_type]) 2);
by (rtac oallI 1);
by (forward_tac [ltD RSN (3, refl RS lemma2)] 1
        THEN assume_tac 2);
by (fast_tac (claset() addSEs [fun_type_gen]) 1);
by (eresolve_tac [ltD RSN (3, refl RS lemma3) RS ssubst] 1
        THEN assume_tac 2);
by (fast_tac (claset() addSEs [fun_type_gen]) 1);
by (fast_tac (claset() addss (simpset())) 1);
qed "DC0_DC_nat";

(* ************************************************************************
   DC(omega) ==> DC                                                       
                                                                          
   The scheme of the proof:                                               
                                                                          
   Assume DC(omega). Let R and x satisfy the premise of DC.               
                                                                          
   Define XX and RR as follows:                                           
                                                                          
    XX = (UN n:nat. {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R})

    RR = {<z1,z2>:Fin(XX)*XX. 
           (domain(z2)=succ(UN f:z1. domain(f)) &
	    (ALL f:z1. restrict(z2, domain(f)) = f)) |      
	   (~ (EX g:XX. domain(g)=succ(UN f:z1. domain(f)) &
	                (ALL f:z1. restrict(g, domain(f)) = f)) &           
	    z2={<0,x>})}                                          
                                                                          
   Then XX and RR satisfy the hypotheses of DC(omega).                    
   So applying DC:                                                        
                                                                          
         EX f:nat->XX. ALL n:nat. f``n RR f`n                             
                                                                          
   Thence                                                                 
                                                                          
         ff = {<n, f`n`n>. n:nat}                                         
                                                                          
   is the desired function.                                               
                                                                          
************************************************************************* *)

goalw thy [lesspoll_def, Finite_def]
        "!!A. A lesspoll nat ==> Finite(A)";
by (fast_tac (claset() addSDs [ltD, lepoll_imp_ex_le_eqpoll]
        addSIs [Ord_nat]) 1);
qed "lesspoll_nat_is_Finite";

goal thy "!!n. n:nat ==> ALL A. (A eqpoll n & A <= X) --> A : Fin(X)";
by (etac nat_induct 1);
by (rtac allI 1);
by (fast_tac (claset() addSIs [Fin.emptyI]
        addSDs [eqpoll_imp_lepoll RS lepoll_0_is_0]) 1);
by (rtac allI 1);
by (rtac impI 1);
by (etac conjE 1);
by (resolve_tac [eqpoll_succ_imp_not_empty RS not_emptyE] 1
        THEN (assume_tac 1));
by (forward_tac [Diff_sing_eqpoll] 1 THEN (assume_tac 1));
by (etac allE 1);
by (etac impE 1);
by (Fast_tac 1);
by (dtac subsetD 1 THEN (assume_tac 1));
by (dresolve_tac [Fin.consI] 1 THEN (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [cons_Diff]) 1);
qed "Finite_Fin_lemma";

goalw thy [Finite_def] "!!A. [| Finite(A); A <= X |] ==> A : Fin(X)";
by (etac bexE 1);
by (dtac Finite_Fin_lemma 1);
by (etac allE 1);
by (etac impE 1);
by (assume_tac 2);
by (Fast_tac 1);
qed "Finite_Fin";

goal thy "!!x. x: X  \
\ ==> {<0,x>}: (UN n:nat. {f:succ(n)->X. ALL k:n. <f`k, f`succ(k)> : R})";
by (rtac (nat_0I RS UN_I) 1);
by (fast_tac (claset() addSIs [singleton_fun RS Pi_type]
        addss (simpset() addsimps [singleton_0 RS sym])) 1);
qed "singleton_in_funs";

goal thy
        "!!X. [| XX = (UN n:nat.  \
\               {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       RR = {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(UN f:z1. domain(f))  \
\       & (ALL f:z1. restrict(z2, domain(f)) = f)) |  \
\       (~ (EX g:XX. domain(g)=succ(UN f:z1. domain(f))  \
\       & (ALL f:z1. restrict(g, domain(f)) = f)) & z2={<0,x>})};  \
\       range(R) <= domain(R); x:domain(R)  \
\       |] ==> RR <= Pow(XX)*XX &  \
\       (ALL Y:Pow(XX). Y lesspoll nat --> (EX x:XX. <Y,x>:RR))";
by (rtac conjI 1);
by (deepen_tac (claset() addSEs [FinD RS PowI]) 0 1);
by (rtac (impI RS ballI) 1);
by (dresolve_tac [[lesspoll_nat_is_Finite, PowD] MRS Finite_Fin] 1
        THEN (assume_tac 1));
by (excluded_middle_tac "EX g:XX. domain(g)=succ(UN f:Y. domain(f))  \
\       & (ALL f:Y. restrict(g, domain(f)) = f)" 1);
by (etac subst 2 THEN (*elimination equation for greater speed*)
    fast_tac (claset() addss (simpset())) 2);
by (safe_tac (claset() delrules [domainE]));
by (swap_res_tac [bexI] 1 THEN etac singleton_in_funs 2);
by (asm_full_simp_tac (simpset() addsimps [nat_0I  RSN (2, bexI), 
                                     cons_fun_type2, empty_fun]) 1);
val lemma4 = result();

goal thy "!!f. [| f:nat->X; n:nat |] ==>  \
\       (UN x:f``succ(n). P(x)) =  P(f`n) Un (UN x:f``n. P(x))";
by (asm_full_simp_tac (simpset()
        addsimps [Ord_nat RSN (2, OrdmemD) RSN (2, image_fun),
        [nat_succI, Ord_nat] MRS OrdmemD RSN (2, image_fun)]) 1);
qed "UN_image_succ_eq";

goal thy "!!f. [| (UN x:f``n. P(x)) = y; P(f`n) = succ(y);  \
\       f:nat -> X; n:nat |] ==> (UN x:f``succ(n). P(x)) = succ(y)";
by (asm_full_simp_tac (simpset() addsimps [UN_image_succ_eq]) 1);
by (Fast_tac 1);
qed "UN_image_succ_eq_succ";

goal thy "!!f. [| f:succ(n) -> D;  n:nat;  \
\       domain(f)=succ(x); x=y |] ==> f`y : D";
by (fast_tac (claset() addEs [apply_type]
        addSDs [[sym, domain_of_fun] MRS trans]) 1);
qed "apply_domain_type";

goal thy "!!f. [| f : nat -> X; n:nat |] ==> f``succ(n) = cons(f`n, f``n)";
by (asm_full_simp_tac (simpset()
        addsimps [nat_succI, Ord_nat RSN (2, OrdmemD), image_fun]) 1);
qed "image_fun_succ";

goal thy "!!f. [| domain(f`n) = succ(u); f : nat -> (UN n:nat.  \
\       {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       u=k; n:nat  \
\       |] ==> f`n : succ(k) -> domain(R)";
by (dtac apply_type 1 THEN (assume_tac 1));
by (fast_tac (claset() addEs [UN_E, domain_eq_imp_fun_type]) 1);
qed "f_n_type";

goal thy "!!f. [| f : nat -> (UN n:nat.  \
\       {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       domain(f`n) = succ(k); n:nat  \
\       |] ==> ALL i:k. <f`n`i, f`n`succ(i)> : R";
by (dtac apply_type 1 THEN (assume_tac 1));
by (etac UN_E 1);
by (etac CollectE 1);
by (dresolve_tac [domain_of_fun RS sym RS trans] 1 THEN (assume_tac 1));
by (Asm_full_simp_tac 1);
qed "f_n_pairs_in_R";

goalw thy [restrict_def]
        "!!f. [| restrict(f, domain(x))=x; f:n->X; domain(x) <= n  \
\       |] ==> restrict(cons(<n, y>, f), domain(x)) = x";
by (eresolve_tac [sym RS trans RS sym] 1);
by (rtac fun_extension 1);
by (fast_tac (claset() addSIs [lam_type]) 1);
by (fast_tac (claset() addSIs [lam_type]) 1);
by (asm_full_simp_tac (simpset() addsimps [subsetD RS cons_val_k]) 1);
qed "restrict_cons_eq_restrict";

goal thy "!!f. [| ALL x:f``n. restrict(f`n, domain(x))=x;  \
\       f : nat -> (UN n:nat.  \
\       {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       n:nat; domain(f`n) = succ(n);  \
\       (UN x:f``n. domain(x)) <= n |] \
\       ==> ALL x:f``succ(n). restrict(cons(<succ(n),y>, f`n), domain(x))=x";
by (rtac ballI 1);
by (asm_full_simp_tac (simpset() addsimps [image_fun_succ]) 1);
by (dtac f_n_type 1 THEN REPEAT (ares_tac [refl] 1));
by (etac disjE 1);
by (asm_full_simp_tac (simpset() addsimps [domain_of_fun, restrict_cons_eq]) 1);
by (dtac bspec 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [restrict_cons_eq_restrict]) 1);
qed "all_in_image_restrict_eq";

goal thy
"!!X.[| ALL b<nat. <f``b, f`b> :  \
\       {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(UN f:z1. domain(f))  & \
\                            (ALL f:z1. restrict(z2, domain(f)) = f)) |  \
\                    (~ (EX g:XX. domain(g)=succ(UN f:z1. domain(f)) & \
\                                 (ALL f:z1. restrict(g, domain(f)) = f)) & \
\                            z2={<0,x>})};  \
\       XX = (UN n:nat.  \
\       {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       f: nat -> XX; range(R) <= domain(R); x:domain(R)  \
\    |] ==> ALL b<nat. <f``b, f`b> :  \
\           {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(UN f:z1. domain(f))  \
\           & (UN f:z1. domain(f)) = b  \
\           & (ALL f:z1. restrict(z2, domain(f)) = f))}";
by (rtac oallI 1);
by (dtac ltD 1);
by (etac nat_induct 1);
by (dresolve_tac [[nat_0I, Ord_nat] MRS ltI RSN (2, ospec)] 1);
by (fast_tac (FOL_cs addss
              (simpset() addsimps [singleton_fun RS domain_of_fun,
                                  singleton_0, singleton_in_funs])) 1);
(*induction step*) (** LEVEL 5 **)
by (full_simp_tac (*prevent simplification of ~EX to ALL~*)
		  (FOL_ss addsimps [separation, split]) 1);
by (dresolve_tac [[nat_succI, Ord_nat] MRS ltI RSN (2, ospec)] 1
        THEN (assume_tac 1));
by (REPEAT (eresolve_tac [conjE, disjE] 1));
by (fast_tac (FOL_cs addSEs [trans, subst_context]
                     addSIs [UN_image_succ_eq_succ] addss (simpset())) 1);
by (etac conjE 1);
by (etac notE 1);
by (asm_full_simp_tac (simpset() addsimps [UN_image_succ_eq_succ]) 1);
(** LEVEL 12 **)
by (REPEAT (eresolve_tac [conjE, bexE] 1));
by (dtac apply_domain_type 1 THEN REPEAT (assume_tac 1));
by (etac domainE 1);
by (etac domainE 1);

by (forward_tac [f_n_type] 1 THEN REPEAT (assume_tac 1));

by (rtac bexI 1);
by (etac nat_succI 2);
by (res_inst_tac [("x","cons(<succ(xa), ya>, f`xa)")] bexI 1);
by (rtac conjI 1);
by (fast_tac (FOL_cs
        addEs [subst_context RSN (2, trans) RS domain_cons_eq_succ,
        subst_context, all_in_image_restrict_eq, trans, equalityD1]) 2);
by (eresolve_tac [rangeI RSN (2, subsetD) RSN (2, cons_fun_type2)] 2
        THEN REPEAT (assume_tac 2));
by (rtac ballI 1);
by (etac succE 1);
(** LEVEL 25 **)
by (dresolve_tac [domain_of_fun RSN (2, f_n_pairs_in_R)] 2
        THEN REPEAT (assume_tac 2));
by (dtac bspec 2 THEN (assume_tac 2));
by (asm_full_simp_tac (simpset()
        addsimps [nat_into_Ord RS succ_in_succ, succI2, cons_val_k]) 2);
by (asm_full_simp_tac (simpset() addsimps [cons_val_n, cons_val_k]) 1);
qed "simplify_recursion";


goal thy "!!X. [| XX = (UN n:nat.  \
\               {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       ALL b<nat. <f``b, f`b> :  \
\       {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(UN f:z1. domain(f))  \
\       & (UN f:z1. domain(f)) = b  \
\       & (ALL f:z1. restrict(z2, domain(f)) = f))};  \
\       f: nat -> XX; range(R) <= domain(R); x:domain(R); n:nat  \
\       |] ==> f`n : succ(n) -> domain(R)  \
\       & (ALL i:n. <f`n`i, f`n`succ(i)>:R)";
by (dtac ospec 1);
by (eresolve_tac [Ord_nat RSN (2, ltI)] 1);
by (etac CollectE 1);
by (Asm_full_simp_tac 1);
by (rtac conjI 1);
by (fast_tac (claset()
        addSEs [trans RS domain_eq_imp_fun_type, subst_context]) 1);
by (fast_tac (FOL_cs addSEs [conjE, f_n_pairs_in_R, trans, subst_context]) 1);
val lemma2 = result();

goal thy 
"!!n. [| XX = (UN n:nat.  \
\                {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R});  \
\       ALL b<nat. <f``b, f`b> :  \
\              {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(UN f:z1. domain(f))  \
\       & (UN f:z1. domain(f)) = b  \
\       & (ALL f:z1. restrict(z2, domain(f)) = f))};  \
\       f : nat -> XX;  n:nat;  range(R) <= domain(R);  x:domain(R)  \
\       |] ==> f`n`n = f`succ(n)`n";
by (forward_tac [lemma2 RS conjunct1 RS domain_of_fun] 1
        THEN REPEAT (assume_tac 1));
by (dresolve_tac [[nat_succI, Ord_nat] MRS ltI RSN (2, ospec)] 1
        THEN (assume_tac 1));
by (Asm_full_simp_tac 1);
by (REPEAT (etac conjE 1));
by (etac ballE 1);
by (eresolve_tac [restrict_eq_imp_val_eq RS sym] 1);
by (fast_tac (claset() addSEs [ssubst]) 1);
by (asm_full_simp_tac (simpset()
        addsimps [[nat_succI, Ord_nat] MRS OrdmemD RSN (2, image_fun)]) 1);
val lemma3 = result();


goalw thy [DC_def, DC0_def] "!!Z. DC(nat) ==> DC0";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [asm_rl, conjE, ex_in_domain RS exE, allE] 1));
by (eresolve_tac [[refl, refl] MRS lemma4 RSN (2, impE)] 1
        THEN REPEAT (assume_tac 1));
by (etac bexE 1);
by (dresolve_tac [refl RSN (2, simplify_recursion)] 1
        THEN REPEAT (assume_tac 1));
by (res_inst_tac [("x","lam n:nat. f`n`n")] bexI 1);
by (rtac lam_type 2);
by (eresolve_tac [[refl RS lemma2 RS conjunct1, succI1] MRS apply_type] 2
        THEN REPEAT (assume_tac 2));
by (rtac ballI 1);
by (forward_tac [refl RS (nat_succI RSN (6, lemma2)) RS conjunct2] 1
        THEN REPEAT (assume_tac 1));
by (dresolve_tac [refl RS lemma3] 1 THEN REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [nat_succI]) 1);
qed "DC_nat_DC0";

(* ********************************************************************** *)
(* ALL K. Card(K) --> DC(K) ==> WO3                                       *)
(* ********************************************************************** *)

goalw thy [lesspoll_def]
        "!!A. [| ~ A lesspoll B; C lesspoll B |] ==> A - C ~= 0";
by (fast_tac (claset() addSDs [Diff_eq_0_iff RS iffD1 RS subset_imp_lepoll]
        addSIs [eqpollI] addEs [notE] addSEs [eqpollE, lepoll_trans]) 1);
val lesspoll_lemma = result();

val [f_type, Ord_a, not_eq] = goalw thy [inj_def]
        "[| f:a->X; Ord(a); (!!b c. [| b<c; c:a |] ==> f`b~=f`c)  \
\       |] ==> f:inj(a, X)";
by (resolve_tac [f_type RS CollectI] 1);
by (REPEAT (resolve_tac [ballI,impI] 1));
by (resolve_tac [Ord_a RS Ord_in_Ord RS Ord_linear_lt] 1
        THEN (assume_tac 1));
by (eres_inst_tac [("j","x")] (Ord_a RS Ord_in_Ord) 1);
by (REPEAT (fast_tac (claset() addDs [not_eq, not_eq RS not_sym]) 1));
qed "fun_Ord_inj";

goal thy "!!a. [| f:X->Y; A<=X; a:A |] ==> f`a : f``A";
by (fast_tac (claset() addSEs [image_fun RS ssubst]) 1);
qed "value_in_image";

goalw thy [DC_def, WO3_def]
        "!!Z. ALL K. Card(K) --> DC(K) ==> WO3";
by (rtac allI 1);
by (excluded_middle_tac "A lesspoll Hartog(A)" 1);
by (fast_tac (claset() addSDs [lesspoll_imp_ex_lt_eqpoll]
        addSIs [Ord_Hartog, leI RS le_imp_subset]) 2);
by (REPEAT (eresolve_tac [allE, impE] 1));
by (rtac Card_Hartog 1);
by (eres_inst_tac [("x","A")] allE 1);
by (eres_inst_tac [("x","{<z1,z2>:Pow(A)*A . z1  \
\               lesspoll Hartog(A) & z2 ~: z1}")] allE 1);
by (Asm_full_simp_tac 1);
by (etac impE 1);
by (fast_tac (claset() addEs [lesspoll_lemma RS not_emptyE]) 1);
by (etac bexE 1);
by (resolve_tac [exI RS (lepoll_def RS (def_imp_iff RS iffD2))
        RS (HartogI RS notE)] 1);
by (resolve_tac [Ord_Hartog RSN (2, fun_Ord_inj)] 1 THEN (assume_tac 1));
by (dresolve_tac [Ord_Hartog RSN (2, OrdmemD) RSN (2,
        ltD RSN (3, value_in_image))] 1 
        THEN REPEAT (assume_tac 1));
by (fast_tac (claset() addSDs [Ord_Hartog RSN (2, ltI) RSN (2, ospec)]
        addEs [subst]) 1);
qed "DC_WO3";

(* ********************************************************************** *)
(* WO1 ==> ALL K. Card(K) --> DC(K)                                       *)
(* ********************************************************************** *)

goal thy
        "!!a. [| Ord(a); b:a |] ==> (lam x:a. P(x))``b = (lam x:b. P(x))``b";
by (rtac images_eq 1);
by (REPEAT (fast_tac (claset() addSEs [RepFunI, OrdmemD]
        addSIs [lam_type]) 2));
by (rtac ballI 1);
by (dresolve_tac [OrdmemD RS subsetD] 1
        THEN REPEAT (assume_tac 1));
by (Asm_full_simp_tac 1);
qed "lam_images_eq";

goalw thy [lesspoll_def] "!!K. [| Card(K); b:K |] ==> b lesspoll K";
by (asm_full_simp_tac (simpset() addsimps [Card_iff_initial]) 1);
by (fast_tac (claset() addSIs [le_imp_lepoll, ltI, leI]) 1);
qed "in_Card_imp_lesspoll";

goal thy "(lam b:a. P(b)) : a -> {P(b). b:a}";
by (fast_tac (claset() addSIs [lam_type, RepFunI]) 1);
qed "lam_type_RepFun";

goal thy "!!Z. [| ALL Y:Pow(X). Y lesspoll a --> (EX x:X. <Y, x> : R);  \
\       b:a; Z:Pow(X); Z lesspoll a |]  \
\       ==> {x:X. <Z,x> : R} ~= 0";
by (fast_tac (FOL_cs addEs [bexE, equals0D]
        addSDs [bspec] addIs [CollectI]) 1);
val lemma_ = result();

goal thy "!!K. [| Card(K); well_ord(X,Q);  \
\       ALL Y:Pow(X). Y lesspoll K --> (EX x:X. <Y, x> : R); b:K |]  \
\       ==> ff(b, X, Q, R) : {x:X. <(lam c:b. ff(c, X, Q, R))``b, x> : R}";
by (res_inst_tac [("P","b:K")] impE 1 THEN TRYALL assume_tac);
by (res_inst_tac [("i","b")] (Card_is_Ord RS Ord_in_Ord RS trans_induct) 1
        THEN REPEAT (assume_tac 1));
by (rtac impI 1);
by (resolve_tac [ff_def RS def_transrec RS ssubst] 1);
by (etac the_first_in 1);
by (Fast_tac 1);
by (asm_full_simp_tac (simpset()
        addsimps [[lam_type_RepFun, subset_refl] MRS image_fun]) 1);
by (etac lemma_ 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [RepFunE, impE, notE]
                addEs [Card_is_Ord RSN (2, OrdmemD) RS subsetD]) 1);
by (fast_tac (claset() addSEs [[in_Card_imp_lesspoll, RepFun_lepoll]
                MRS lepoll_lesspoll_lesspoll]) 1);
val lemma = result();

goalw thy [DC_def, WO1_def]
        "!!Z. WO1 ==> ALL K. Card(K) --> DC(K)";
by (REPEAT (resolve_tac [allI,impI] 1));
by (REPEAT (eresolve_tac [allE,exE,conjE] 1));
by (res_inst_tac [("x","lam b:K. ff(b, X, Ra, R)")] bexI 1);
by (rtac lam_type 2);
by (resolve_tac [lemma RS CollectD1] 2 THEN REPEAT (assume_tac 2));
by (asm_full_simp_tac (simpset()
        addsimps [[Card_is_Ord, ltD] MRS lam_images_eq]) 1);
by (fast_tac (claset() addSEs [ltE, lemma RS CollectD2]) 1);
qed" WO1_DC_Card";

