(*  Title:      ZF/AC/WO6_WO1.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of "WO6 ==> WO1".  Simplified by L C Paulson.

From the book "Equivalents of the Axiom of Choice" by Rubin & Rubin,
pages 2-5
*)

open WO6_WO1;

goal OrderType.thy 
      "!!i j k. [| k < i++j;  Ord(i);  Ord(j) |] ==>  \
\                  k < i  |  (~ k<i & k = i ++ (k--i) & (k--i)<j)";
by (res_inst_tac [("i","k"),("j","i")] Ord_linear2 1);
by (dtac odiff_lt_mono2 4 THEN assume_tac 4);
by (asm_full_simp_tac
    (!simpset addsimps [oadd_odiff_inverse, odiff_oadd_inverse]) 4);
by (safe_tac (!claset addSEs [lt_Ord]));
qed "lt_oadd_odiff_disj";

(*The corresponding elimination rule*)
val lt_oadd_odiff_cases = rule_by_tactic (safe_tac (!claset))
                                         (lt_oadd_odiff_disj RS disjE);

(* ********************************************************************** *)
(* The most complicated part of the proof - lemma ii - p. 2-4             *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* some properties of relation uu(beta, gamma, delta) - p. 2              *)
(* ********************************************************************** *)

goalw thy [uu_def] "domain(uu(f,b,g,d)) <= f`b";
by (Blast_tac 1);
qed "domain_uu_subset";

goal thy "!! a. ALL b<a. f`b lepoll m ==> \
\               ALL b<a. ALL g<a. ALL d<a. domain(uu(f,b,g,d)) lepoll m";
by (fast_tac (!claset addSEs
        [domain_uu_subset RS subset_imp_lepoll RS lepoll_trans]) 1);
qed "quant_domain_uu_lepoll_m";

goalw thy [uu_def] "uu(f,b,g,d) <= f`b * f`g";
by (Blast_tac 1);
qed "uu_subset1";

goalw thy [uu_def] "uu(f,b,g,d) <= f`d";
by (Blast_tac 1);
qed "uu_subset2";

goal thy "!! a. [| ALL b<a. f`b lepoll m;  d<a |] ==> uu(f,b,g,d) lepoll m";
by (fast_tac (!claset
        addSEs [uu_subset2 RS subset_imp_lepoll RS lepoll_trans]) 1);
qed "uu_lepoll_m";

(* ********************************************************************** *)
(* Two cases for lemma ii                                                 *)
(* ********************************************************************** *)
goalw thy [lesspoll_def] 
  "!! a f u. ALL b<a. ALL g<a. ALL d<a. u(f,b,g,d) lepoll m ==>  \
\            (ALL b<a. f`b ~= 0 --> (EX g<a. EX d<a. u(f,b,g,d) ~= 0 &  \
\                                       u(f,b,g,d) lesspoll m)) |  \
\            (EX b<a. f`b ~= 0 & (ALL g<a. ALL d<a. u(f,b,g,d) ~= 0 -->  \
\                                       u(f,b,g,d) eqpoll m))";
by (Asm_simp_tac 1);
by (blast_tac (!claset delrules [equalityI]) 1);
qed "cases";

(* ********************************************************************** *)
(* Lemmas used in both cases                                              *)
(* ********************************************************************** *)
goal thy "!!a C. Ord(a) ==> (UN b<a++a. C(b)) = (UN b<a. C(b) Un C(a++b))";
by (fast_tac (!claset addSIs [equalityI] addIs [ltI] 
                    addSDs [lt_oadd_disj]
                    addSEs [lt_oadd1, oadd_lt_mono2]) 1);
qed "UN_oadd";


(* ********************************************************************** *)
(* Case 1 : lemmas                                                        *)
(* ********************************************************************** *)

goalw thy [vv1_def] "vv1(f,m,b) <= f`b";
by (rtac (LetI RS LetI) 1);
by (split_tac [expand_if] 1);
by (simp_tac (!simpset addsimps [domain_uu_subset]) 1);
qed "vv1_subset";

(* ********************************************************************** *)
(* Case 1 : Union of images is the whole "y"                              *)
(* ********************************************************************** *)
goalw thy [gg1_def]
  "!! a f y. [| Ord(a);  m:nat |] ==>   \
\            (UN b<a++a. gg1(f,a,m)`b) = (UN b<a. f`b)";
by (asm_simp_tac
    (!simpset addsimps [UN_oadd, lt_oadd1,
                           oadd_le_self RS le_imp_not_lt, lt_Ord,
                           odiff_oadd_inverse, ltD,
                           vv1_subset RS Diff_partition, ww1_def]) 1);
qed "UN_gg1_eq";

goal thy "domain(gg1(f,a,m)) = a++a";
by (simp_tac (!simpset addsimps [lam_funtype RS domain_of_fun, gg1_def]) 1);
qed "domain_gg1";

(* ********************************************************************** *)
(* every value of defined function is less than or equipollent to m       *)
(* ********************************************************************** *)
goal thy "!!a b. [| P(a, b);  Ord(a);  Ord(b);  \
\               Least_a = (LEAST a. EX x. Ord(x) & P(a, x)) |]  \
\               ==> P(Least_a, LEAST b. P(Least_a, b))";
by (etac ssubst 1);
by (res_inst_tac [("Q","%z. P(z, LEAST b. P(z, b))")] LeastI2 1);
by (REPEAT (fast_tac (!claset addSEs [LeastI]) 1));
qed "nested_LeastI";

val nested_Least_instance = 
   standard
     (read_instantiate 
        [("P","%g d. domain(uu(f,b,g,d)) ~= 0 &  \
\               domain(uu(f,b,g,d)) lepoll m")] nested_LeastI);

goalw thy [gg1_def]
    "!!a. [| Ord(a);  m:nat;  \
\            ALL b<a. f`b ~=0 -->                                       \
\            (EX g<a. EX d<a. domain(uu(f,b,g,d)) ~= 0  &               \
\                             domain(uu(f,b,g,d)) lepoll m);            \
\            ALL b<a. f`b lepoll succ(m);  b<a++a                       \
\         |] ==> gg1(f,a,m)`b lepoll m";
by (Asm_simp_tac 1);
by (safe_tac (!claset addSEs [lt_oadd_odiff_cases]));
(*Case b<a   : show vv1(f,m,b) lepoll m *)
by (asm_simp_tac (!simpset addsimps [vv1_def, Let_def] 
                        setloop split_tac [expand_if]) 1);
by (fast_tac (!claset addIs [nested_Least_instance RS conjunct2]
                addSEs [lt_Ord]
                addSIs [empty_lepollI]) 1);
(*Case a le b: show ww1(f,m,b--a) lepoll m *)
by (asm_simp_tac (!simpset addsimps [ww1_def]) 1);
by (excluded_middle_tac "f`(b--a) = 0" 1);
by (asm_simp_tac (!simpset addsimps [empty_lepollI]) 2);
by (rtac Diff_lepoll 1);
by (Blast_tac 1);
by (rtac vv1_subset 1);
by (dtac (ospec RS mp) 1);
by (REPEAT (eresolve_tac [asm_rl, oexE] 1));
by (asm_simp_tac (!simpset
        addsimps [vv1_def, Let_def, lt_Ord, 
                  nested_Least_instance RS conjunct1]) 1);
qed "gg1_lepoll_m";

(* ********************************************************************** *)
(* Case 2 : lemmas                                                        *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* Case 2 : vv2_subset                                                    *)
(* ********************************************************************** *)

goalw thy [uu_def] "!!f. [| b<a;  g<a;  f`b~=0;  f`g~=0;        \
\                           y*y <= y;  (UN b<a. f`b)=y          \
\                        |] ==> EX d<a. uu(f,b,g,d) ~= 0";
by (fast_tac (!claset addSIs [not_emptyI] 
                    addSDs [SigmaI RSN (2, subsetD)]
                    addSEs [not_emptyE]) 1);
qed "ex_d_uu_not_empty";

goal thy "!!f. [| b<a; g<a; f`b~=0; f`g~=0;  \
\                       y*y<=y; (UN b<a. f`b)=y |]  \
\               ==> uu(f,b,g,LEAST d. (uu(f,b,g,d) ~= 0)) ~= 0";
by (dtac ex_d_uu_not_empty 1 THEN REPEAT (assume_tac 1));
by (fast_tac (!claset addSEs [LeastI, lt_Ord]) 1);
qed "uu_not_empty";

goal ZF.thy "!!r. [| r<=A*B; r~=0 |] ==> domain(r)~=0";
by (REPEAT (eresolve_tac [asm_rl, not_emptyE, subsetD RS SigmaE, 
                sym RSN (2, subst_elem) RS domainI RS not_emptyI] 1));
qed "not_empty_rel_imp_domain";

goal thy "!!f. [| b<a; g<a; f`b~=0; f`g~=0;  \
\                       y*y <= y; (UN b<a. f`b)=y |]  \
\               ==> (LEAST d. uu(f,b,g,d) ~= 0) < a";
by (eresolve_tac [ex_d_uu_not_empty RS oexE] 1
        THEN REPEAT (assume_tac 1));
by (resolve_tac [Least_le RS lt_trans1] 1
        THEN (REPEAT (ares_tac [lt_Ord] 1)));
qed "Least_uu_not_empty_lt_a";

goal ZF.thy "!!B. [| B<=A; a~:B |] ==> B <= A-{a}";
by (Blast_tac 1);
qed "subset_Diff_sing";

(*Could this be proved more directly?*)
goal thy "!!A B. [| A lepoll m; m lepoll B; B <= A; m:nat |] ==> A=B";
by (etac natE 1);
by (fast_tac (!claset addSDs [lepoll_0_is_0] addSIs [equalityI]) 1);
by (hyp_subst_tac 1);
by (rtac equalityI 1);
by (assume_tac 2);
by (rtac subsetI 1);
by (excluded_middle_tac "?P" 1 THEN (assume_tac 2));
by (eresolve_tac [subset_Diff_sing RS subset_imp_lepoll RSN (2, 
                Diff_sing_lepoll RSN (3, lepoll_trans RS lepoll_trans)) RS 
                succ_lepoll_natE] 1
        THEN REPEAT (assume_tac 1));
qed "supset_lepoll_imp_eq";

goal thy
 "!!a. [| ALL g<a. ALL d<a. domain(uu(f, b, g, d))~=0 -->               \
\         domain(uu(f, b, g, d)) eqpoll succ(m);                        \
\         ALL b<a. f`b lepoll succ(m);  y*y <= y;                       \
\         (UN b<a. f`b)=y;  b<a;  g<a;  d<a;                            \
\         f`b~=0;  f`g~=0;  m:nat;  s:f`b                               \
\      |] ==> uu(f, b, g, LEAST d. uu(f,b,g,d)~=0) : f`b -> f`g";
by (dres_inst_tac [("x2","g")] (ospec RS ospec RS mp) 1);
by (rtac ([uu_subset1, uu_not_empty] MRS not_empty_rel_imp_domain) 3);
by (rtac Least_uu_not_empty_lt_a 2 THEN TRYALL assume_tac);
by (resolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RS 
        (Least_uu_not_empty_lt_a RSN (2, uu_lepoll_m) RSN (2, 
        uu_subset1 RSN (4, rel_is_fun)))] 1
        THEN TRYALL assume_tac);
by (rtac (eqpoll_sym RS eqpoll_imp_lepoll RSN (2, supset_lepoll_imp_eq)) 1);
by (REPEAT (fast_tac (!claset addSIs [domain_uu_subset, nat_succI]) 1));
qed "uu_Least_is_fun";

goalw thy [vv2_def]
    "!!a. [| ALL g<a. ALL d<a. domain(uu(f, b, g, d))~=0 -->            \
\            domain(uu(f, b, g, d)) eqpoll succ(m);                     \
\            ALL b<a. f`b lepoll succ(m); y*y <= y;                     \
\            (UN b<a. f`b)=y;  b<a;  g<a;  m:nat;  s:f`b                \
\          |] ==> vv2(f,b,g,s) <= f`g";
by (split_tac [expand_if] 1);
by Safe_tac;
by (etac (uu_Least_is_fun RS apply_type) 1);
by (REPEAT_SOME (fast_tac (!claset addSIs [not_emptyI, singleton_subsetI])));
qed "vv2_subset";

(* ********************************************************************** *)
(* Case 2 : Union of images is the whole "y"                              *)
(* ********************************************************************** *)
goalw thy [gg2_def]
    "!!a. [| ALL g<a. ALL d<a. domain(uu(f,b,g,d)) ~= 0 -->             \
\            domain(uu(f,b,g,d)) eqpoll succ(m);                        \
\            ALL b<a. f`b lepoll succ(m); y*y<=y;                       \
\            (UN b<a. f`b)=y;  Ord(a);  m:nat;  s:f`b;  b<a              \
\         |] ==> (UN g<a++a. gg2(f,a,b,s) ` g) = y";
by (dtac sym 1);
by (asm_simp_tac
    (!simpset addsimps [UN_oadd, lt_oadd1,
                           oadd_le_self RS le_imp_not_lt, lt_Ord,
                           odiff_oadd_inverse, ww2_def,
                           vv2_subset RS Diff_partition]) 1);
qed "UN_gg2_eq";

goal thy "domain(gg2(f,a,b,s)) = a++a";
by (simp_tac (!simpset addsimps [lam_funtype RS domain_of_fun, gg2_def]) 1);
qed "domain_gg2";

(* ********************************************************************** *)
(* every value of defined function is less than or equipollent to m       *)
(* ********************************************************************** *)

goalw thy [vv2_def]
    "!!m. [| m:nat; m~=0 |] ==> vv2(f,b,g,s) lepoll m";
by (asm_simp_tac (!simpset addsimps [empty_lepollI]
                              setloop split_tac [expand_if]) 1);
by (fast_tac (!claset
        addSDs [le_imp_subset RS subset_imp_lepoll RS lepoll_0_is_0]
        addSIs [singleton_eqpoll_1 RS eqpoll_imp_lepoll RS lepoll_trans,
                not_lt_imp_le RS le_imp_subset RS subset_imp_lepoll,
                nat_into_Ord, nat_1I]) 1);
qed "vv2_lepoll";

goalw thy [ww2_def]
    "!!m. [| ALL b<a. f`b lepoll succ(m);  g<a;  m:nat;  vv2(f,b,g,d) <= f`g  \
\         |] ==> ww2(f,b,g,d) lepoll m";
by (excluded_middle_tac "f`g = 0" 1);
by (asm_simp_tac (!simpset addsimps [empty_lepollI]) 2);
by (dtac ospec 1 THEN (assume_tac 1));
by (rtac Diff_lepoll 1
        THEN (TRYALL assume_tac));
by (asm_simp_tac (!simpset addsimps [vv2_def, expand_if, not_emptyI]) 1);
qed "ww2_lepoll";

goalw thy [gg2_def]
    "!!a. [| ALL g<a. ALL d<a. domain(uu(f,b,g,d)) ~= 0 -->             \
\            domain(uu(f,b,g,d)) eqpoll succ(m);                        \
\            ALL b<a. f`b lepoll succ(m);  y*y <= y;                    \
\            (UN b<a. f`b)=y;  b<a;  s:f`b;  m:nat;  m~= 0;  g<a++a     \
\         |] ==> gg2(f,a,b,s) ` g lepoll m";
by (Asm_simp_tac 1);
by (safe_tac (!claset addSEs [lt_oadd_odiff_cases, lt_Ord2]));
by (asm_simp_tac (!simpset addsimps [vv2_lepoll]) 1);
by (asm_simp_tac (!simpset addsimps [ww2_lepoll, vv2_subset]) 1);
qed "gg2_lepoll_m";

(* ********************************************************************** *)
(* lemma ii                                                               *)
(* ********************************************************************** *)
goalw thy [NN_def]
        "!!y. [| succ(m) : NN(y); y*y <= y; m:nat; m~=0 |] ==> m : NN(y)";
by (REPEAT (eresolve_tac [CollectE, exE, conjE] 1));
by (resolve_tac [quant_domain_uu_lepoll_m RS cases RS disjE] 1
    THEN (assume_tac 1));
(* case 1 *)
by (asm_full_simp_tac (!simpset addsimps [lesspoll_succ_iff]) 1);
by (res_inst_tac [("x","a++a")] exI 1);
by (fast_tac (!claset addSIs [Ord_oadd, domain_gg1, UN_gg1_eq, 
                                  gg1_lepoll_m]) 1);
(* case 2 *)
by (REPEAT (eresolve_tac [oexE, conjE] 1));
by (res_inst_tac [("A","f`?B")] not_emptyE 1 THEN (assume_tac 1));
by (rtac CollectI 1);
by (etac succ_natD 1);
by (res_inst_tac [("x","a++a")] exI 1);
by (res_inst_tac [("x","gg2(f,a,b,x)")] exI 1);
(*Calling fast_tac might get rid of the res_inst_tac calls, but it
  is just too slow.*)
by (asm_simp_tac (!simpset addsimps 
                  [Ord_oadd, domain_gg2, UN_gg2_eq, gg2_lepoll_m]) 1);
qed "lemma_ii";


(* ********************************************************************** *)
(* lemma iv - p. 4 :                                                      *)
(* For every set x there is a set y such that   x Un (y * y) <= y         *)
(* ********************************************************************** *)

(* the quantifier ALL looks inelegant but makes the proofs shorter  *)
(* (used only in the following two lemmas)                          *)

goal thy "ALL n:nat. rec(n, x, %k r. r Un r*r) <=  \
\                    rec(succ(n), x, %k r. r Un r*r)";
by (fast_tac (!claset addIs [rec_succ RS ssubst]) 1);
qed "z_n_subset_z_succ_n";

goal thy "!!n. [| ALL n:nat. f(n)<=f(succ(n)); n le m; n : nat; m: nat |]  \
\              ==> f(n)<=f(m)";
by (eres_inst_tac [("P","n le m")] rev_mp 1);
by (res_inst_tac [("P","%z. n le z --> f(n) <= f(z)")] nat_induct 1);
by (REPEAT (fast_tac le_cs 1));
qed "le_subsets";

goal thy "!!n m. [| n le m; m:nat |] ==>  \
\       rec(n, x, %k r. r Un r*r) <= rec(m, x, %k r. r Un r*r)";
by (resolve_tac [z_n_subset_z_succ_n RS le_subsets] 1 
    THEN (TRYALL assume_tac));
by (eresolve_tac [Ord_nat RSN (2, ltI) RSN (2, lt_trans1) RS ltD] 1
    THEN (assume_tac 1));
qed "le_imp_rec_subset";

goal thy "EX y. x Un y*y <= y";
by (res_inst_tac [("x","UN n:nat. rec(n, x, %k r. r Un r*r)")] exI 1);
by (safe_tac (!claset));
by (rtac (nat_0I RS UN_I) 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("a","succ(n Un na)")] UN_I 1);
by (eresolve_tac [Un_nat_type RS nat_succI] 1 THEN (assume_tac 1));
by (fast_tac (ZF_cs addIs [le_imp_rec_subset RS subsetD]
                addSIs [Un_upper1_le, Un_upper2_le, Un_nat_type]
                addSEs [nat_into_Ord] addss (!simpset)) 1);
qed "lemma_iv";

(* ********************************************************************** *)
(* Rubin & Rubin wrote :                                                  *)
(* "It follows from (ii) and mathematical induction that if y*y <= y then *)
(* y can be well-ordered"                                                 *)

(* In fact we have to prove :                                             *)
(*      * WO6 ==> NN(y) ~= 0                                              *)
(*      * reverse induction which lets us infer that 1 : NN(y)            *)
(*      * 1 : NN(y) ==> y can be well-ordered                             *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(*      WO6 ==> NN(y) ~= 0                                                *)
(* ********************************************************************** *)

goalw thy [WO6_def, NN_def] "!!y. WO6 ==> NN(y) ~= 0";
by (fast_tac (ZF_cs addEs [equals0D]) 1);
qed "WO6_imp_NN_not_empty";

(* ********************************************************************** *)
(*      1 : NN(y) ==> y can be well-ordered                               *)
(* ********************************************************************** *)

goal thy "!!f. [| (UN b<a. f`b)=y; x:y; ALL b<a. f`b lepoll 1; Ord(a) |]  \
\               ==> EX c<a. f`c = {x}";
by (fast_tac (!claset addSEs [lepoll_1_is_sing]) 1);
val lemma1 = result();

goal thy "!!f. [| (UN b<a. f`b)=y; x:y; ALL b<a. f`b lepoll 1; Ord(a) |]  \
\               ==> f` (LEAST i. f`i = {x}) = {x}";
by (dtac lemma1 1 THEN REPEAT (assume_tac 1));
by (fast_tac (!claset addSEs [lt_Ord] addIs [LeastI]) 1);
val lemma2 = result();

goalw thy [NN_def] "!!y. 1 : NN(y) ==> EX a f. Ord(a) & f:inj(y, a)";
by (etac CollectE 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (res_inst_tac [("x","a")] exI 1);
by (res_inst_tac [("x","lam x:y. LEAST i. f`i = {x}")] exI 1);
by (rtac conjI 1 THEN (assume_tac 1));
by (res_inst_tac [("d","%i. THE x. x:f`i")] lam_injective 1);
by (dtac lemma1 1 THEN REPEAT (assume_tac 1));
by (fast_tac (!claset addSEs [Least_le RS lt_trans1 RS ltD, lt_Ord]) 1);
by (resolve_tac [lemma2 RS ssubst] 1 THEN REPEAT (assume_tac 1));
by (fast_tac (!claset addSIs [the_equality]) 1);
qed "NN_imp_ex_inj";

goal thy "!!y. [| y*y <= y; 1 : NN(y) |] ==> EX r. well_ord(y, r)";
by (dtac NN_imp_ex_inj 1);
by (fast_tac (!claset addSEs [well_ord_Memrel RSN (2,  well_ord_rvimage)]) 1);
qed "y_well_ord";

(* ********************************************************************** *)
(*      reverse induction which lets us infer that 1 : NN(y)              *)
(* ********************************************************************** *)

val [prem1, prem2] = goal thy
        "[| n:nat; !!m. [| m:nat; m~=0; P(succ(m)) |] ==> P(m) |]  \
\       ==> n~=0 --> P(n) --> P(1)";
by (res_inst_tac [("n","n")] nat_induct 1);
by (rtac prem1 1);
by (Blast_tac 1);
by (excluded_middle_tac "x=0" 1);
by (Blast_tac 2);
by (fast_tac (!claset addSIs [prem2]) 1);
qed "rev_induct_lemma";

val prems = goal thy
        "[| P(n); n:nat; n~=0;  \
\       !!m. [| m:nat; m~=0; P(succ(m)) |] ==> P(m) |]  \
\       ==> P(1)";
by (resolve_tac [rev_induct_lemma RS impE] 1);
by (etac impE 4 THEN (assume_tac 5));
by (REPEAT (ares_tac prems 1));
qed "rev_induct";

goalw thy [NN_def] "!!n. n:NN(y) ==> n:nat";
by (etac CollectD1 1);
qed "NN_into_nat";

goal thy "!!n. [| n:NN(y); y*y <= y; n~=0 |] ==> 1:NN(y)";
by (rtac rev_induct 1 THEN REPEAT (ares_tac [NN_into_nat] 1));
by (rtac lemma_ii 1 THEN REPEAT (assume_tac 1));
val lemma3 = result();

(* ********************************************************************** *)
(* Main theorem "WO6 ==> WO1"                                             *)
(* ********************************************************************** *)

(* another helpful lemma *)
goalw thy [NN_def] "!!y. 0:NN(y) ==> y=0";
by (fast_tac (!claset addSIs [equalityI] 
                    addSDs [lepoll_0_is_0] addEs [subst]) 1);
qed "NN_y_0";

goalw thy [WO1_def] "!!Z. WO6 ==> WO1";
by (rtac allI 1);
by (excluded_middle_tac "A=0" 1);
by (fast_tac (!claset addSIs [well_ord_Memrel, nat_0I RS nat_into_Ord]) 2);
by (res_inst_tac [("x1","A")] (lemma_iv RS revcut_rl) 1);
by (etac exE 1);
by (dtac WO6_imp_NN_not_empty 1);
by (eresolve_tac [Un_subset_iff RS iffD1 RS conjE] 1);
by (eres_inst_tac [("A","NN(y)")] not_emptyE 1);
by (forward_tac [y_well_ord] 1);
by (fast_tac (!claset addEs [well_ord_subset]) 2);
by (fast_tac (!claset addSIs [lemma3] addSDs [NN_y_0] addSEs [not_emptyE]) 1);
qed "WO6_imp_WO1";

