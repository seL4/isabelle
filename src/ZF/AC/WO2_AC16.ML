(*  Title:      ZF/AC/WO2_AC16.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

  The proof of WO2 ==> AC16(k #+ m, k)
  
  The main part of the proof is the inductive reasoning concerning
  properties of constructed family T_gamma.
  The proof deals with three cases for ordinals: 0, succ and limit ordinal.
  The first instance is trivial, the third not difficult, but the second
  is very complicated requiring many lemmas.
  We also need to prove that at any stage gamma the set 
  (s - Union(...) - k_gamma)   (Rubin & Rubin page 15)
  contains m distinct elements (in fact is equipollent to s)
*)

(* ********************************************************************** *)
(* case of limit ordinal                                                  *)
(* ********************************************************************** *)

goal thy "!!Z. [| ALL y<x. ALL z<a. z<y | (EX Y: F(y). f(z)<=Y)  \
\               --> (EX! Y. Y:F(y) & f(z)<=Y);  \
\               ALL i j. i le j --> F(i) <= F(j); j le i; i<x; z<a;  \
\               V: F(i); f(z)<=V; W:F(j); f(z)<=W |]  \
\               ==> V = W";
by (REPEAT (eresolve_tac [asm_rl, allE, impE] 1));
by (dtac subsetD 1 THEN (assume_tac 1));
by (REPEAT (dtac ospec 1 THEN (assume_tac 1)));
by (eresolve_tac [disjI2 RSN (2, impE)] 1);
by (fast_tac (FOL_cs addSIs [bexI]) 1);
by (etac ex1_two_eq 1 THEN (REPEAT (ares_tac [conjI] 1)));
val lemma3_1 = result();

goal thy "!!Z. [| ALL y<x. ALL z<a. z<y | (EX Y: F(y). f(z)<=Y)  \
\               --> (EX! Y. Y:F(y) & f(z)<=Y);  \
\               ALL i j. i le j --> F(i) <= F(j); i<x; j<x; z<a;  \
\               V: F(i); f(z)<=V; W:F(j); f(z)<=W |]  \
\               ==> V = W";
by (res_inst_tac [("j","j")] (lt_Ord RS (lt_Ord RSN (2, Ord_linear_le))) 1
        THEN (REPEAT (assume_tac 1)));
by (eresolve_tac [lemma3_1 RS sym] 1 THEN (REPEAT (assume_tac 1)));
by (etac lemma3_1 1 THEN (REPEAT (assume_tac 1)));
val lemma3 = result();

goal thy "!!a. [| ALL y<x. F(y) <= X &  \
\               (ALL x<a. x < y | (EX Y:F(y). fa(x) <= Y) -->  \
\                       (EX! Y. Y : F(y) & fa(x) <= Y)); x < a |]  \
\               ==> ALL y<x. ALL z<a. z < y | (EX Y:F(y). fa(z) <= Y) -->  \
\                       (EX! Y. Y : F(y) & fa(z) <= Y)";
by (REPEAT (resolve_tac [oallI, impI] 1));
by (dresolve_tac [ospec] 1 THEN (assume_tac 1));
by (fast_tac (FOL_cs addSEs [oallE]) 1);
val lemma4 = result();

goal thy "!!a. [| ALL y<x. F(y) <= X &  \
\               (ALL x<a. x < y | (EX Y:F(y). fa(x) <= Y) -->  \
\                       (EX! Y. Y : F(y) & fa(x) <= Y)); \
\               x < a; Limit(x); ALL i j. i le j --> F(i) <= F(j) |]  \
\               ==> (UN x<x. F(x)) <= X &  \
\               (ALL xa<a. xa < x | (EX x:UN x<x. F(x). fa(xa) <= x)  \
\               --> (EX! Y. Y : (UN x<x. F(x)) & fa(xa) <= Y))";
by (rtac conjI 1);
by (rtac subsetI 1);
by (etac OUN_E 1);
by (dresolve_tac [ospec] 1 THEN (assume_tac 1));
by (Fast_tac 1);
by (dtac lemma4 1 THEN (assume_tac 1));
by (rtac oallI 1);
by (rtac impI 1);
by (etac disjE 1);
by (forward_tac [Limit_has_succ RSN (2, ospec)] 1 THEN (REPEAT (assume_tac 1)));
by (dres_inst_tac [("A","a"),("x","xa")] ospec 1 THEN (assume_tac 1));
by (eresolve_tac [lt_Ord RS le_refl RSN (2, disjI1 RSN (2, impE))] 1
        THEN (assume_tac 1));
by (REPEAT (eresolve_tac [ex1E, conjE] 1));
by (rtac ex1I 1);
by (rtac conjI 1 THEN (assume_tac 2));
by (eresolve_tac [Limit_has_succ RS OUN_I] 1 THEN (TRYALL assume_tac));
by (REPEAT (eresolve_tac [conjE, OUN_E] 1));
by (etac lemma3 1 THEN (TRYALL assume_tac));
by (etac Limit_has_succ 1 THEN (assume_tac 1));
by (etac bexE 1);
by (rtac ex1I 1);
by (etac conjI 1 THEN (assume_tac 1));
by (REPEAT (eresolve_tac [conjE, OUN_E] 1));
by (etac lemma3 1 THEN (TRYALL assume_tac));
val lemma5 = result();

(* ********************************************************************** *)
(* case of successor ordinal                                              *)
(* ********************************************************************** *)

(*
  First quite complicated proof of the fact used in the recursive construction
  of the family T_gamma (WO2 ==> AC16(k #+ m, k)) - the fact that at any stage
  gamma the set (s - Union(...) - k_gamma) is equipollent to s
  (Rubin & Rubin page 15).
*)

(* ********************************************************************** *)
(* dbl_Diff_eqpoll_Card                                                   *)
(* ********************************************************************** *)

goal thy "!!A. [| A eqpoll a; Card(a); ~Finite(a); B lesspoll a;  \
\       C lesspoll a |] ==> A - B - C eqpoll a";
by (rtac Diff_lesspoll_eqpoll_Card 1 THEN (REPEAT (assume_tac 1)));
by (rtac Diff_lesspoll_eqpoll_Card 1 THEN (REPEAT (assume_tac 1)));
val dbl_Diff_eqpoll_Card = result();

(* ********************************************************************** *)
(* Case of finite ordinals                                                *)
(* ********************************************************************** *)

goalw thy [lesspoll_def]
        "!!X. [| Finite(X); ~Finite(a); Ord(a) |] ==> X lesspoll a";
by (rtac conjI 1);
by (dresolve_tac [nat_le_infinite_Ord RS le_imp_lepoll] 1
        THEN (assume_tac 1));
by (rewtac Finite_def);
by (fast_tac (!claset addSEs [eqpoll_sym RS eqpoll_trans]) 2);
by (rtac lepoll_trans 1 THEN (assume_tac 2));
by (fast_tac (!claset addSEs [Ord_nat RSN (2, ltI) RS leI RS le_imp_subset RS 
        subset_imp_lepoll RSN (2, eqpoll_imp_lepoll RS lepoll_trans)]) 1);
val Finite_lesspoll_infinite_Ord = result();

goal thy "!!x. x:X ==> Union(X) = Union(X-{x}) Un x";
by (fast_tac eq_cs 1);
val Union_eq_Un_Diff = result();

goal thy "!!n. n:nat ==> ALL X. X eqpoll n --> (ALL x:X. Finite(x))  \
\       --> Finite(Union(X))";
by (etac nat_induct 1);
by (fast_tac (!claset addSDs [eqpoll_imp_lepoll RS lepoll_0_is_0]
        addSIs [nat_0I RS nat_into_Finite] addss (!simpset)) 1);
by (REPEAT (resolve_tac [allI, impI] 1));
by (resolve_tac [eqpoll_succ_imp_not_empty RS not_emptyE] 1 THEN (assume_tac 1));
by (res_inst_tac [("P","%z. Finite(z)")] (Union_eq_Un_Diff RS ssubst) 1
        THEN (assume_tac 1));
by (rtac Finite_Un 1);
by (Fast_tac 2);
by (fast_tac (!claset addSIs [Diff_sing_eqpoll]) 1);
val Finite_Union_lemma = result();

goal thy "!!X. [| ALL x:X. Finite(x); Finite(X) |] ==> Finite(Union(X))";
by (eresolve_tac [Finite_def RS def_imp_iff RS iffD1 RS bexE] 1);
by (dtac Finite_Union_lemma 1);
by (Fast_tac 1);
val Finite_Union = result();

goalw thy [Finite_def] "!!x. [| x lepoll n; n:nat |] ==> Finite(x)";
by (fast_tac (!claset
        addEs [nat_into_Ord RSN (2, lepoll_imp_ex_le_eqpoll) RS exE,
        Ord_nat RSN (2, ltI) RSN (2, lt_trans1) RS ltD]) 1);
val lepoll_nat_num_imp_Finite = result();

goal thy "!!X. [| ALL x:X. x lepoll n & x <= T; well_ord(T, R); X lepoll b;  \
\       b<a; ~Finite(a); Card(a); n:nat |]  \
\       ==> Union(X) lesspoll a";
by (excluded_middle_tac "Finite(X)" 1);
by (resolve_tac [Card_is_Ord RSN (3, Finite_lesspoll_infinite_Ord)] 2
        THEN (REPEAT (assume_tac 3)));
by (fast_tac (!claset addSEs [lepoll_nat_num_imp_Finite]
                addSIs [Finite_Union]) 2);
by (dresolve_tac [lt_Ord RSN (2, lepoll_imp_ex_le_eqpoll)] 1 THEN (assume_tac 1));
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (forward_tac [eqpoll_imp_lepoll RS lepoll_infinite] 1 THEN (assume_tac 1));
by (eresolve_tac [eqpoll_sym RS (eqpoll_def RS def_imp_iff RS iffD1) RS
                exE] 1);
by (forward_tac [bij_is_surj RS surj_image_eq] 1);
by (dresolve_tac [[bij_is_fun, subset_refl] MRS image_fun] 1);
by (dresolve_tac [sym RS trans] 1 THEN (assume_tac 1));
by (hyp_subst_tac 1);
by (rtac lepoll_lesspoll_lesspoll 1);
by (eresolve_tac [lt_trans1 RSN (2, lt_Card_imp_lesspoll)] 1
        THEN REPEAT (assume_tac 1));
by (rtac UN_lepoll 1
        THEN (TRYALL (fast_tac (!claset addSEs [lt_Ord]))));
val Union_lesspoll = result();

(* ********************************************************************** *)
(* recfunAC16_lepoll_index                                                *)
(* ********************************************************************** *)

goal thy "A Un {a} = cons(a, A)";
by (fast_tac eq_cs 1);
val Un_sing_eq_cons = result();

goal thy "!!A. A lepoll B ==> A Un {a} lepoll succ(B)";
by (asm_simp_tac (!simpset addsimps [Un_sing_eq_cons, succ_def]) 1);
by (eresolve_tac [mem_not_refl RSN (2, cons_lepoll_cong)] 1);
val Un_lepoll_succ = result();

goal thy "!!a. Ord(a) ==> F(a) - (UN b<succ(a). F(b)) = 0";
by (fast_tac (!claset addSIs [OUN_I, le_refl] addIs [equalityI]) 1);
val Diff_UN_succ_empty = result();

goal thy "!!a. Ord(a) ==> F(a) Un X - (UN b<succ(a). F(b)) <= X";
by (fast_tac (!claset addSIs [OUN_I, le_refl]) 1);
val Diff_UN_succ_subset = result();

goal thy "!!x. Ord(x) ==>  \
\       recfunAC16(f, g, x, a) - (UN i<x. recfunAC16(f, g, i, a)) lepoll 1";
by (etac Ord_cases 1);
by (asm_simp_tac (!simpset addsimps [recfunAC16_0,
                empty_subsetI RS subset_imp_lepoll]) 1);
by (asm_simp_tac (!simpset addsimps [recfunAC16_Limit,
                Diff_cancel, empty_subsetI RS subset_imp_lepoll]) 2);
by (asm_simp_tac (!simpset addsimps [recfunAC16_succ]) 1);
by (resolve_tac [conjI RS (expand_if RS iffD2)] 1);
by (fast_tac (!claset addSIs [empty_subsetI RS subset_imp_lepoll]
                addSEs [Diff_UN_succ_empty RS ssubst]) 1);
by (fast_tac (!claset addSEs [Diff_UN_succ_subset RS subset_imp_lepoll RS
        (singleton_eqpoll_1 RS eqpoll_imp_lepoll RSN (2, lepoll_trans))]) 1);
val recfunAC16_Diff_lepoll_1 = result();

goal thy "!!z. [| z : F(x); Ord(x) |]  \
\       ==> z:F(LEAST i. z:F(i)) - (UN j<(LEAST i. z:F(i)). F(j))";
by (fast_tac (!claset addEs [less_LeastE] addSEs [OUN_E, LeastI]) 1);
val in_Least_Diff = result();

goal thy "!!w. [| (LEAST i. w:F(i)) = (LEAST i. z:F(i));  \
\       w:(UN i<a. F(i)); z:(UN i<a. F(i)) |]  \
\       ==> EX b<a. w:(F(b) - (UN c<b. F(c))) & z:(F(b) - (UN c<b. F(c)))";
by (REPEAT (etac OUN_E 1));
by (dresolve_tac [lt_Ord RSN (2, in_Least_Diff)] 1 THEN (assume_tac 1));
by (forward_tac [lt_Ord RSN (2, in_Least_Diff)] 1 THEN (assume_tac 1));
by (rtac oexI 1);
by (rtac conjI 1 THEN (assume_tac 2));
by (etac subst 1 THEN (assume_tac 1));
by (eresolve_tac [lt_Ord RSN (2, Least_le) RS lt_trans1] 1
        THEN (REPEAT (assume_tac 1)));
val Least_eq_imp_ex = result();

goal thy "!!A. [| A lepoll 1; a:A; b:A |] ==> a=b";
by (fast_tac (!claset addSDs [lepoll_1_is_sing]) 1);
val two_in_lepoll_1 = result();

goal thy "!!a. [| ALL i<a. F(i)-(UN j<i. F(j)) lepoll 1; Limit(a) |]  \
\       ==> (UN x<a. F(x)) lepoll a";
by (resolve_tac [lepoll_def RS (def_imp_iff RS iffD2)] 1);
by (res_inst_tac [("x","lam z: (UN x<a. F(x)). LEAST i. z:F(i)")] exI 1);
by (rewtac inj_def);
by (rtac CollectI 1);
by (rtac lam_type 1);
by (etac OUN_E 1);
by (etac Least_in_Ord 1);
by (etac ltD 1);
by (etac lt_Ord2 1);
by (rtac ballI 1);
by (rtac ballI 1);
by (Asm_simp_tac 1);
by (rtac impI 1);
by (dtac Least_eq_imp_ex 1 THEN (REPEAT (assume_tac 1)));
by (fast_tac (!claset addSEs [two_in_lepoll_1]) 1);
val UN_lepoll_index = result();

goal thy "!!y. Ord(y) ==> recfunAC16(f, fa, y, a) lepoll y";
by (etac trans_induct 1);
by (etac Ord_cases 1);
by (asm_simp_tac (!simpset addsimps [recfunAC16_0, lepoll_refl]) 1);
by (asm_simp_tac (!simpset addsimps [recfunAC16_succ]) 1);
by (fast_tac (!claset addIs [conjI RS (expand_if RS iffD2)]
        addSDs [succI1 RSN (2, bspec)]
        addSEs [subset_succI RS subset_imp_lepoll RSN (2, lepoll_trans),
                Un_lepoll_succ]) 1);
by (asm_simp_tac (!simpset addsimps [recfunAC16_Limit]) 1);
by (fast_tac (!claset addSEs [lt_Ord RS recfunAC16_Diff_lepoll_1]
        addSIs [UN_lepoll_index]) 1);
val recfunAC16_lepoll_index = result();

goal thy "!!y. [| recfunAC16(f,g,y,a) <= {X: Pow(A). X eqpoll n};  \
\               A eqpoll a; y<a; ~Finite(a); Card(a); n:nat |]  \
\               ==> Union(recfunAC16(f,g,y,a)) lesspoll a";
by (eresolve_tac [eqpoll_def RS def_imp_iff RS iffD1 RS exE] 1);
by (rtac Union_lesspoll 1 THEN (TRYALL assume_tac));
by (eresolve_tac [lt_Ord RS recfunAC16_lepoll_index] 3);
by (eresolve_tac [[bij_is_inj, Card_is_Ord RS well_ord_Memrel] MRS
        well_ord_rvimage] 2 THEN (assume_tac 2));
by (fast_tac (!claset addSEs [eqpoll_imp_lepoll]) 1);
val Union_recfunAC16_lesspoll = result();

goal thy
  "!!a. [| recfunAC16(f, fa, y, a) <= {X: Pow(A) . X eqpoll succ(k #+ m)};  \
\       Card(a); ~ Finite(a); A eqpoll a;  \
\       k : nat; m : nat; y<a;  \
\       fa : bij(a, {Y: Pow(A). Y eqpoll succ(k)}) |]  \
\       ==> A - Union(recfunAC16(f, fa, y, a)) - fa`y eqpoll a";
by (rtac dbl_Diff_eqpoll_Card 1 THEN (TRYALL assume_tac));
by (rtac Union_recfunAC16_lesspoll 1 THEN (REPEAT (assume_tac 1)));
by (eresolve_tac [add_type RS nat_succI] 1 THEN (assume_tac 1));
by (resolve_tac [nat_succI RSN (2, bexI RS (Finite_def RS def_imp_iff RS
        iffD2)) RS (Card_is_Ord RSN (3, Finite_lesspoll_infinite_Ord))] 1
        THEN (TRYALL assume_tac));
by (eresolve_tac [ltD RSN (2, bij_is_fun RS apply_type) RS CollectE] 1
        THEN (TRYALL assume_tac));
val dbl_Diff_eqpoll = result();

(* back to the proof *)

val disj_Un_eqpoll_nat_sum = disj_Un_eqpoll_sum RS (
                             sum_eqpoll_cong RSN (2, 
                             nat_sum_eqpoll_sum RSN (3, 
                             eqpoll_trans RS eqpoll_trans))) |> standard;

goal thy "!!x. [| x : Pow(A - B - fa`i); x eqpoll m;  \
\       fa : bij(a, {x: Pow(A) . x eqpoll k}); i<a; k:nat; m:nat |]  \
\       ==> fa ` i Un x : {x: Pow(A) . x eqpoll k #+ m}";
by (rtac CollectI 1);
by (fast_tac (!claset addSIs [PowD RS (PowD RSN (2, Un_least RS PowI))] 
        addSEs [ltD RSN (2, bij_is_fun RS apply_type RS CollectE)]) 1);
by (rtac disj_Un_eqpoll_nat_sum 1
        THEN (TRYALL assume_tac));
by (fast_tac (!claset addSIs [equals0I]) 1);
by (eresolve_tac [ltD RSN (2, bij_is_fun RS apply_type RS CollectE)] 1
        THEN (REPEAT (assume_tac 1)));
val Un_in_Collect = result();

(* ********************************************************************** *)
(* Lemmas simplifying assumptions                                         *)
(* ********************************************************************** *)

goal thy "!!j. [| ALL y<succ(j). F(y)<=X & (ALL x<a. x<y | P(x,y)  \
\       --> Q(x,y)); succ(j)<a |]  \
\       ==> F(j)<=X & (ALL x<a. x<j | P(x,j) --> Q(x,j))";
by (dresolve_tac [ospec] 1);
by (resolve_tac [lt_Ord RS (succI1 RS ltI RS lt_Ord RS le_refl)] 1
        THEN (REPEAT (assume_tac 1)));
val lemma6 = result();

goal thy "!!j. [| F(j)<=X; (ALL x<a. x<j | P(x,j) --> Q(x,j)); succ(j)<a |]  \
\       ==> P(j,j) --> F(j) <= X & (ALL x<a. x le j | P(x,j) --> Q(x,j))";
by (fast_tac (!claset addSEs [leE]) 1);
val lemma7 = result();

(* ********************************************************************** *)
(* Lemmas needded to prove ex_next_set which means that for any successor *)
(* ordinal there is a set satisfying certain properties                   *)
(* ********************************************************************** *)

goal thy "!!A. [| A eqpoll a; ~ Finite(a); Ord(a); m:nat |]  \
\       ==> EX X:Pow(A). X eqpoll m";
by (eresolve_tac [Ord_nat RSN (2, ltI) RS 
                (nat_le_infinite_Ord RSN (2, lt_trans2)) RS 
                leI RS le_imp_lepoll RS 
                ((eqpoll_sym RS eqpoll_imp_lepoll) RSN (2, lepoll_trans)) RS 
                lepoll_imp_eqpoll_subset RS exE] 1 
        THEN REPEAT (assume_tac 1));
by (fast_tac (!claset addSEs [eqpoll_sym]) 1);
val ex_subset_eqpoll = result();

goal thy "!!A. [| A <= B Un C; A Int C = 0 |] ==> A <= B";
by (fast_tac (!claset addDs [equals0D]) 1);
val subset_Un_disjoint = result();

goal thy "!!F. [| X:Pow(A - Union(B) -C); T:B; F<=T |] ==> F Int X = 0";
by (fast_tac (!claset addSIs [equals0I]) 1);
val Int_empty = result();

(* ********************************************************************** *)
(* equipollent subset (and finite) is the whole set                       *)
(* ********************************************************************** *)

goal thy "!!A. [| A <= B; a : A; A - {a} = B - {a} |] ==> A = B";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Diffs_eq_imp_eq = result();

goal thy "!!A. m:nat ==> ALL A B. A <= B & m lepoll A & B lepoll m --> A=B";
by (etac nat_induct 1);
by (fast_tac (!claset addSDs [lepoll_0_is_0] addSIs [equalityI]) 1);
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (etac conjE 1));
by (resolve_tac [succ_lepoll_imp_not_empty RS not_emptyE] 1
        THEN (assume_tac 1));
by (forward_tac [subsetD RS Diff_sing_lepoll] 1
        THEN REPEAT (assume_tac 1));
by (forward_tac [lepoll_Diff_sing] 1);
by (REPEAT (eresolve_tac [allE, impE] 1));
by (rtac conjI 1);
by (Fast_tac 2);
by (Fast_tac 1);
by (etac Diffs_eq_imp_eq 1
        THEN REPEAT (assume_tac 1));
val subset_imp_eq_lemma = result();

goal thy "!!A. [| A <= B; m lepoll A; B lepoll m; m:nat |] ==> A=B";
by (fast_tac (FOL_cs addSDs [subset_imp_eq_lemma]) 1);
val subset_imp_eq = result();

goal thy "!!f. [| f:bij(a, {Y:X. Y eqpoll succ(k)}); k:nat; f`b<=f`y; b<a;  \
\       y<a |] ==> b=y";
by (dtac subset_imp_eq 1);
by (etac nat_succI 3);
by (fast_tac (!claset addSEs [bij_is_fun RS (ltD RSN (2, apply_type)) RS
                CollectE, eqpoll_sym RS eqpoll_imp_lepoll]) 1);
by (fast_tac (!claset addSEs [bij_is_fun RS (ltD RSN (2, apply_type)) RS
        CollectE, eqpoll_imp_lepoll]) 1);
by (rewrite_goals_tac [bij_def, inj_def]);
by (fast_tac (!claset addSDs [ltD]) 1);
val bij_imp_arg_eq = result();

goal thy
  "!!a. [| recfunAC16(f, fa, y, a) <= {X: Pow(A) . X eqpoll succ(k #+ m)};  \
\       Card(a); ~ Finite(a); A eqpoll a;  \
\       k : nat; m : nat; y<a;  \
\       fa : bij(a, {Y: Pow(A). Y eqpoll succ(k)});  \
\       ~ (EX Y:recfunAC16(f, fa, y, a). fa`y <= Y) |]  \
\       ==> EX X:{Y: Pow(A). Y eqpoll succ(k #+ m)}. fa`y <= X &  \
\               (ALL b<a. fa`b <= X -->  \
\               (ALL T:recfunAC16(f, fa, y, a). ~ fa`b <= T))";
by (eresolve_tac [dbl_Diff_eqpoll RS ex_subset_eqpoll RS bexE] 1
        THEN REPEAT (assume_tac 1));
by (etac Card_is_Ord 1);
by (forward_tac [Un_in_Collect] 2 THEN REPEAT (assume_tac 2));
by (etac CollectE 4);
by (rtac bexI 4);
by (rtac CollectI 5);
by (assume_tac 5);
by (eresolve_tac [add_succ RS subst] 5);
by (assume_tac 1);
by (etac nat_succI 1);
by (assume_tac 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (REPEAT (resolve_tac [ballI, impI, oallI, notI] 1));
by (dresolve_tac [Int_empty RSN (2, subset_Un_disjoint)] 1
        THEN REPEAT (assume_tac 1));
by (dtac bij_imp_arg_eq 1 THEN REPEAT (assume_tac 1));
by (hyp_subst_tac 1);
by (eresolve_tac [bexI RSN (2, notE)] 1 THEN TRYALL assume_tac);
val ex_next_set = result();

(* ********************************************************************** *)
(* Lemma ex_next_Ord states that for any successor                        *)
(* ordinal there is a number of the set satisfying certain properties     *)
(* ********************************************************************** *)

goal thy
  "!!a. [| recfunAC16(f, fa, y, a) <= {X: Pow(A) . X eqpoll succ(k #+ m)};  \
\       Card(a); ~ Finite(a); A eqpoll a;  \
\       k : nat; m : nat; y<a;  \
\       fa : bij(a, {Y: Pow(A). Y eqpoll succ(k)});  \
\       f : bij(a, {Y: Pow(A). Y eqpoll succ(k #+ m)});  \
\       ~ (EX Y:recfunAC16(f, fa, y, a). fa`y <= Y) |]  \
\       ==> EX c<a. fa`y <= f`c &  \
\               (ALL b<a. fa`b <= f`c -->  \
\               (ALL T:recfunAC16(f, fa, y, a). ~ fa`b <= T))";
by (dtac ex_next_set 1 THEN REPEAT (assume_tac 1));
by (etac bexE 1);
by (resolve_tac [bij_converse_bij RS bij_is_fun RS apply_type RS ltI RSN
        (2, oexI)] 1);
by (resolve_tac [right_inverse_bij RS ssubst] 1
        THEN REPEAT (ares_tac [Card_is_Ord] 1));
val ex_next_Ord = result();

goal thy "!!Z. [| EX! Y. Y:Z & P(Y); ~P(W) |] ==> EX! Y. Y:Z Un {W} & P(Y)";
by (Fast_tac 1);
val ex1_in_Un_sing = result();

(* ********************************************************************** *)
(* Lemma simplifying assumptions                                          *)
(* ********************************************************************** *)

goal thy "!!j. [| ALL x<a. x<j | (EX xa:F(j). P(x, xa))  \
\       --> (EX! Y. Y:F(j) & P(x, Y)); F(j) <= X;  \
\       L : X; P(j, L) & (ALL x<a. P(x, L) --> (ALL xa:F(j). ~P(x, xa))) |]  \
\       ==> F(j) Un {L} <= X &  \
\       (ALL x<a. x le j | (EX xa:F(j) Un {L}. P(x, xa)) -->  \
\               (EX! Y. Y:F(j) Un {L} & P(x, Y)))";
by (rtac conjI 1);
by (fast_tac (!claset addSIs [singleton_subsetI]) 1);
by (rtac oallI 1);
by (etac oallE 1 THEN (contr_tac 2));
by (rtac impI 1);
by (etac disjE 1);
by (etac leE 1);
by (eresolve_tac [disjI1 RSN (2, impE)] 1 THEN (assume_tac 1));
by (rtac ex1E 1 THEN (assume_tac 1));
by (etac ex1_in_Un_sing 1);
by (Fast_tac 1);
by (Fast_tac 1);
by (etac bexE 1);
by (etac UnE 1);
by (fast_tac (!claset addSEs [ex1_in_Un_sing]) 1);
by (Fast_tac 1);
val lemma8 = result();

(* ********************************************************************** *)
(* The main part of the proof: inductive proof of the property of T_gamma *)
(* lemma main_induct                                                      *)
(* ********************************************************************** *)

goal thy
        "!!a. [| b < a; f : bij(a, {Y: Pow(A) . Y eqpoll succ(k #+ m)});  \
\       fa : bij(a, {Y: Pow(A) . Y eqpoll succ(k)});  \
\       ~Finite(a); Card(a); A eqpoll a; k : nat; m : nat |]  \
\       ==> recfunAC16(f, fa, b, a) <= {X: Pow(A) . X eqpoll succ(k #+ m)} &  \
\       (ALL x<a. x < b | (EX Y:recfunAC16(f, fa, b, a). fa ` x <= Y) -->  \
\       (EX! Y. Y:recfunAC16(f, fa, b, a) & fa ` x <= Y))";
by (etac lt_induct 1);
by (forward_tac [lt_Ord] 1);
by (etac Ord_cases 1);
(* case 0 *)
by (asm_simp_tac (!simpset addsimps [recfunAC16_0]) 1);
(* case Limit *)
by (asm_simp_tac (!simpset addsimps [recfunAC16_Limit]) 2);
by (rtac lemma5 2 THEN (REPEAT (assume_tac 2)));
by (fast_tac (FOL_cs addSEs [recfunAC16_mono]) 2);
(* case succ *)
by (hyp_subst_tac 1);
by (eresolve_tac [lemma6 RS conjE] 1 THEN (assume_tac 1));
by (asm_simp_tac (!simpset addsimps [recfunAC16_succ]) 1);
by (resolve_tac [conjI RS (expand_if RS iffD2)] 1);
by (etac lemma7 1 THEN (REPEAT (assume_tac 1)));
by (rtac impI 1);
by (resolve_tac [ex_next_Ord RS oexE] 1 
        THEN REPEAT (ares_tac [le_refl RS lt_trans] 1));
by (etac lemma8 1 THEN (assume_tac 1));
by (resolve_tac [bij_is_fun RS apply_type] 1 THEN (assume_tac 1));
by (eresolve_tac [Least_le RS lt_trans2 RS ltD] 1 
        THEN REPEAT (ares_tac [lt_Ord, succ_leI] 1));
(*VERY SLOW!  24 secs??*)
by (eresolve_tac [lt_Ord RSN (2, LeastI)] 1 THEN (assume_tac 1));
val main_induct = result();

(* ********************************************************************** *)
(* Lemma to simplify the inductive proof                                  *)
(*   - the desired property is a consequence of the inductive assumption  *)
(* ********************************************************************** *)

val [prem1, prem2, prem3, prem4] = goal thy
        "[| (!!b. b<a ==> F(b) <= S & (ALL x<a. (x<b | (EX Y:F(b). f`x <= Y)) \
\       --> (EX! Y. Y : F(b) & f`x <= Y)));  \
\       f:a->f``(a); Limit(a); (!!i j. i le j ==> F(i) <= F(j)) |]  \
\       ==> (UN j<a. F(j)) <= S &  \
\       (ALL x:f``a. EX! Y. Y : (UN j<a. F(j)) & x <= Y)";
by (rtac conjI 1);
by (rtac subsetI 1);
by (etac OUN_E 1);
by (dtac prem1 1);
by (Fast_tac 1);
by (rtac ballI 1);
by (etac imageE 1);
by (dresolve_tac [prem3 RS Limit_is_Ord RSN (2, ltI) RS
        (prem3 RS Limit_has_succ)] 1);
by (forward_tac [prem1] 1);
by (etac conjE 1);
by (dresolve_tac [leI RS succ_leE RSN (2, ospec)] 1 THEN (assume_tac 1));
by (etac impE 1);
by (fast_tac (!claset addSEs [leI RS succ_leE RS lt_Ord RS le_refl]) 1);
by (dresolve_tac [prem2 RSN (2, apply_equality)] 1);
by (REPEAT (eresolve_tac [conjE, ex1E] 1));
by (rtac ex1I 1);
by (fast_tac (!claset addSIs [OUN_I]) 1);
by (REPEAT (eresolve_tac [conjE, OUN_E] 1));
by (eresolve_tac [lt_Ord RSN (2, lt_Ord RS Ord_linear_le)] 1 THEN (assume_tac 1));
by (dresolve_tac [prem4 RS subsetD] 2 THEN (assume_tac 2));
by (Fast_tac 2);
by (forward_tac [prem1] 1);
by (forward_tac [succ_leE] 1);
by (dresolve_tac [prem4 RS subsetD] 1 THEN (assume_tac 1));
by (etac conjE 1);
by (dresolve_tac [lt_trans RSN (2, ospec)] 1 THEN (TRYALL assume_tac));
by (dresolve_tac [disjI1 RSN (2, mp)] 1 THEN (assume_tac 1));
by (etac ex1_two_eq 1);
by (REPEAT (Fast_tac 1));
val lemma_simp_induct = result();

(* ********************************************************************** *)
(* The target theorem                                                     *)
(* ********************************************************************** *)

goalw thy [AC16_def]
        "!!n k. [| WO2; 0<m; k:nat; m:nat |] ==> AC16(k #+ m,k)";
by (rtac allI 1);
by (rtac impI 1);
by (forward_tac [WO2_infinite_subsets_eqpoll_X] 1 THEN (REPEAT (assume_tac 1)));
by (forw_inst_tac [("n","k #+ m")] (WO2_infinite_subsets_eqpoll_X) 1
        THEN (REPEAT (ares_tac [add_type] 1)));
by (forward_tac [WO2_imp_ex_Card] 1);
by (REPEAT (eresolve_tac [exE,conjE] 1));
by (dresolve_tac [eqpoll_trans RS eqpoll_sym RS (eqpoll_def RS
        def_imp_iff RS iffD1)] 1 THEN (assume_tac 1));
by (dresolve_tac [eqpoll_trans RS eqpoll_sym RS (eqpoll_def RS
        def_imp_iff RS iffD1)] 1 THEN (assume_tac 1));
by (REPEAT (etac exE 1));
by (res_inst_tac [("x","UN j<a. recfunAC16(fa,f,j,a)")] exI 1);
by (res_inst_tac [("P","%z. ?Y & (ALL x:z. ?Z(x))")] 
        (bij_is_surj RS surj_image_eq RS subst) 1
        THEN (assume_tac 1));
by (rtac lemma_simp_induct 1);
by (eresolve_tac [bij_is_fun RS surj_image RS surj_is_fun] 2);
by (eresolve_tac [eqpoll_imp_lepoll RS lepoll_infinite RS
        infinite_Card_is_InfCard RS InfCard_is_Limit] 2 
        THEN REPEAT (assume_tac 2));
by (etac recfunAC16_mono 2);
by (rtac main_induct 1 
        THEN REPEAT (ares_tac [eqpoll_imp_lepoll RS lepoll_infinite] 1));
qed "WO2_AC16";
