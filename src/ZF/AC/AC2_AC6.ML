(*  Title:      ZF/AC/AC2_AC6.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proofs needed to show that each of AC2, AC3, ..., AC6 is equivalent
to AC0 and AC1:
AC1 ==> AC2 ==> AC1
AC1 ==> AC4 ==> AC3 ==> AC1
AC4 ==> AC5 ==> AC4
AC1 <-> AC6
*)

(* ********************************************************************** *)
(* AC1 ==> AC2                                                            *)
(* ********************************************************************** *)

Goal "[| B:A; f:(PROD X:A. X); 0~:A |]  \
\               ==> {f`B} <= B Int {f`C. C:A}";
by (fast_tac (claset() addSEs [apply_type]) 1);
val lemma1 = result();

Goalw [pairwise_disjoint_def]
        "[| pairwise_disjoint(A); B:A; C:A; D:B; D:C |] ==> f`B = f`C";
by (Fast_tac 1);
val lemma2 = result();

Goalw AC_defs "AC1 ==> AC2"; 
by (rtac allI 1);
by (rtac impI 1);
by (REPEAT (eresolve_tac [asm_rl,conjE,allE,exE,impE] 1));
by (REPEAT (resolve_tac [exI,ballI,equalityI] 1));
by (rtac lemma1 2 THEN (REPEAT (assume_tac 2)));
by (fast_tac (claset() addSEs [lemma2] addEs [apply_type]) 1);
qed "AC1_AC2";


(* ********************************************************************** *)
(* AC2 ==> AC1                                                            *)
(* ********************************************************************** *)

Goal "0~:A ==> 0 ~: {B*{B}. B:A}";
by (fast_tac (claset() addSDs [sym RS (Sigma_empty_iff RS iffD1)]) 1);
val lemma1 = result();

Goal "[| X*{X} Int C = {y}; X:A |]  \
\               ==> (THE y. X*{X} Int C = {y}): X*A";
by (rtac subst_elem 1);
by (fast_tac (claset() addSIs [the_equality]
                addSEs [sym RS trans RS (singleton_eq_iff RS iffD1)]) 2);
by (fast_tac (claset() addSEs [equalityE, make_elim singleton_subsetD]) 1);
val lemma2 = result();

Goal "ALL D:{E*{E}. E:A}. EX y. D Int C = {y}  \
\       ==> (lam x:A. fst(THE z. (x*{x} Int C = {z}))) :  \
\               (PROD X:A. X) ";
by (fast_tac (claset() addSEs [lemma2]
                addSIs [lam_type, RepFunI, fst_type]
                addSDs [bspec]) 1);
val lemma3 = result();

Goalw (AC_defs@AC_aux_defs) "AC2 ==> AC1";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [allE, impE] 1));
by (fast_tac (claset() addSEs [lemma3]) 2);
by (fast_tac (claset() addSIs [lemma1, equals0I]) 1);
qed "AC2_AC1";


(* ********************************************************************** *)
(* AC1 ==> AC4                                                            *)
(* ********************************************************************** *)

Goal "0 ~: {R``{x}. x:domain(R)}";
by (Blast_tac 1);
val lemma = result();

Goalw AC_defs "AC1 ==> AC4";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [allE, lemma RSN (2, impE), exE] 1));
by (best_tac (claset() addSIs [lam_type] addSEs [apply_type]) 1);
qed "AC1_AC4";


(* ********************************************************************** *)
(* AC4 ==> AC3                                                            *)
(* ********************************************************************** *)

Goal "f:A->B ==> (UN z:A. {z}*f`z) <= A*Union(B)";
by (fast_tac (claset() addSDs [apply_type]) 1);
val lemma1 = result();

Goal "domain(UN z:A. {z}*f(z)) = {a:A. f(a)~=0}";
by (fast_tac (claset() addSIs [not_emptyI] addDs [range_type]) 1);
val lemma2 = result();

Goal "x:A ==> (UN z:A. {z}*f(z))``{x} = f(x)";
by (Fast_tac 1);
val lemma3 = result();

Goalw AC_defs "AC4 ==> AC3";
by (REPEAT (resolve_tac [allI,ballI] 1));
by (REPEAT (eresolve_tac [allE,impE] 1));
by (etac lemma1 1);
by (asm_full_simp_tac (simpset() addsimps [lemma2, lemma3]
                        addcongs [Pi_cong]) 1);
qed "AC4_AC3";

(* ********************************************************************** *)
(* AC3 ==> AC1                                                            *)
(* ********************************************************************** *)

Goal "b~:A ==> (PROD x:{a:A. id(A)`a~=b}. id(A)`x) = (PROD x:A. x)";
by (asm_full_simp_tac (simpset() addsimps [id_def] addcongs [Pi_cong]) 1);
by (res_inst_tac [("b","A")] subst_context 1);
by (Fast_tac 1);
val lemma = result();

Goalw AC_defs "AC3 ==> AC1";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [allE, ballE] 1));
by (fast_tac (claset() addSIs [id_type]) 2);
by (fast_tac (claset() addEs [lemma RS subst]) 1);
qed "AC3_AC1";

(* ********************************************************************** *)
(* AC4 ==> AC5                                                            *)
(* ********************************************************************** *)

Goalw (range_def::AC_defs) "AC4 ==> AC5";
by (REPEAT (resolve_tac [allI,ballI] 1));
by (REPEAT (eresolve_tac [allE,impE] 1));
by (eresolve_tac [fun_is_rel RS converse_type] 1);
by (etac exE 1);
by (rtac bexI 1);
by (rtac Pi_type 2 THEN (assume_tac 2));
by (fast_tac (claset() addSDs [apply_type]
        addSEs [fun_is_rel RS converse_type RS subsetD RS SigmaD2]) 2);
by (rtac ballI 1);
by (rtac apply_equality 1 THEN (assume_tac 2));
by (etac domainE 1);
by (ftac range_type 1 THEN (assume_tac 1));
by (fast_tac (claset() addDs [apply_equality]) 1);
qed "AC4_AC5";


(* ********************************************************************** *)
(* AC5 ==> AC4, Rubin & Rubin, p. 11                                      *)
(* ********************************************************************** *)

Goal "R <= A*B ==> (lam x:R. fst(x)) : R -> A";
by (fast_tac (claset() addSIs [lam_type, fst_type]) 1);
val lemma1 = result();

Goalw [range_def] "R <= A*B ==> range(lam x:R. fst(x)) = domain(R)";
by (rtac equalityI 1);
by (fast_tac (claset() addSEs [lamE]
                addEs [subst_elem]
                addSDs [Pair_fst_snd_eq]) 1);
by (rtac subsetI 1);
by (etac domainE 1);
by (rtac domainI 1);
by (fast_tac (claset() addSEs [lamI RS subst_elem] addIs [fst_conv RS ssubst]) 1);
val lemma2 = result();

Goal "[| EX f: A->C. P(f,domain(f)); A=B |] ==>  EX f: B->C. P(f,B)";
by (etac bexE 1);
by (ftac domain_of_fun 1);
by (Fast_tac 1);
val lemma3 = result();

Goal "[| R <= A*B; g: C->R; ALL x:C. (lam z:R. fst(z))` (g`x) = x |] \
\               ==> (lam x:C. snd(g`x)): (PROD x:C. R``{x})";
by (rtac lam_type 1);
by (dtac apply_type 1 THEN (assume_tac 1));
by (dtac bspec 1 THEN (assume_tac 1));
by (rtac imageI 1);
by (resolve_tac [subsetD RS Pair_fst_snd_eq RSN (2, subst_elem)] 1
        THEN (REPEAT (assume_tac 1)));
by (Asm_full_simp_tac 1);
val lemma4 = result();

Goalw AC_defs "AC5 ==> AC4";
by (REPEAT (resolve_tac [allI,impI] 1));
by (REPEAT (eresolve_tac [allE,ballE] 1));
by (eresolve_tac [lemma1 RSN (2, notE)] 2 THEN (assume_tac 2));
by (dresolve_tac [lemma2 RSN (2, lemma3)] 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [lemma4]) 1);
qed "AC5_AC4";


(* ********************************************************************** *)
(* AC1 <-> AC6                                                            *)
(* ********************************************************************** *)

Goalw AC_defs "AC1 <-> AC6";
by (Blast_tac 1);
qed "AC1_iff_AC6";

