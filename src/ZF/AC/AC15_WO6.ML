(*  Title:      ZF/AC/AC15_WO6.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proofs needed to state that AC10, ..., AC15 are equivalent to the rest.
We need the following:

WO1 ==> AC10(n) ==> AC11 ==> AC12 ==> AC15 ==> WO6

In order to add the formulations AC13 and AC14 we need:

AC10(succ(n)) ==> AC13(n) ==> AC14 ==> AC15

or

AC1 ==> AC13(1);  AC13(m) ==> AC13(n) ==> AC14 ==> AC15    (m le n)

So we don't have to prove all implications of both cases.
Moreover we don't need to prove AC13(1) ==> AC1 and AC11 ==> AC14 as
Rubin & Rubin do.
*)

(* ********************************************************************** *)
(* Lemmas used in the proofs in which the conclusion is AC13, AC14        *)
(* or AC15                                                                *)
(*  - cons_times_nat_not_Finite                                           *)
(*  - ex_fun_AC13_AC15                                                    *)
(* ********************************************************************** *)

Goalw [lepoll_def] "A\\<noteq>0 ==> B lepoll A*B";
by (etac not_emptyE 1);
by (res_inst_tac [("x","\\<lambda>z \\<in> B. <x,z>")] exI 1);
by (fast_tac (claset() addSIs [snd_conv, lam_injective]) 1);
qed "lepoll_Sigma";

Goal "0\\<notin>A ==> \\<forall>B \\<in> {cons(0,x*nat). x \\<in> A}. ~Finite(B)";
by (rtac ballI 1);
by (etac RepFunE 1);
by (hyp_subst_tac 1);
by (rtac notI 1);
by (dresolve_tac [subset_consI RS subset_imp_lepoll RS lepoll_Finite] 1);
by (resolve_tac [lepoll_Sigma RS lepoll_Finite RS (nat_not_Finite RS notE)] 1
        THEN (assume_tac 2));
by (Fast_tac 1);
qed "cons_times_nat_not_Finite";

Goal "[| Union(C)=A; a \\<in> A |] ==> \\<exists>B \\<in> C. a \\<in> B & B \\<subseteq> A";
by (Fast_tac 1);
val lemma1 = result();

Goalw [pairwise_disjoint_def]
        "[| pairwise_disjoint(A); B \\<in> A; C \\<in> A; a \\<in> B; a \\<in> C |] ==> B=C";
by (dtac IntI 1 THEN (assume_tac 1));
by (dres_inst_tac [("A","B Int C")] not_emptyI 1);
by (Fast_tac 1);
val lemma2 = result();

Goalw [sets_of_size_between_def]
        "\\<forall>B \\<in> {cons(0, x*nat). x \\<in> A}. pairwise_disjoint(f`B) &  \
\               sets_of_size_between(f`B, 2, n) & Union(f`B)=B  \
\       ==> \\<forall>B \\<in> A. \\<exists>! u. u \\<in> f`cons(0, B*nat) & u \\<subseteq> cons(0, B*nat) &  \
\               0 \\<in> u & 2 lepoll u & u lepoll n";
by (rtac ballI 1);
by (etac ballE 1);
by (Fast_tac 2);
by (REPEAT (etac conjE 1));
by (dresolve_tac [consI1 RSN (2, lemma1)] 1);
by (etac bexE 1);
by (rtac ex1I 1);
by (Fast_tac 1);
by (REPEAT (etac conjE 1));
by (rtac lemma2 1 THEN (REPEAT (assume_tac 1)));
val lemma3 = result();

Goalw [lepoll_def] "[| A lepoll i; Ord(i) |] ==> {P(a). a \\<in> A} lepoll i";
by (etac exE 1);
by (res_inst_tac
        [("x", "\\<lambda>x \\<in> RepFun(A, P). LEAST j. \\<exists>a \\<in> A. x=P(a) & f`a=j")] exI 1);
by (res_inst_tac [("d", "%y. P(converse(f)`y)")] lam_injective 1);
by (etac RepFunE 1);
by (forward_tac [inj_is_fun RS apply_type] 1 THEN (assume_tac 1));
by (fast_tac (claset() addIs [LeastI2]
                addSEs [Ord_in_Ord, inj_is_fun RS apply_type]) 1);
by (etac RepFunE 1);
by (rtac LeastI2 1);
by (Fast_tac 1);
by (fast_tac (claset() addSEs [Ord_in_Ord, inj_is_fun RS apply_type]) 1);
by (fast_tac (claset() addEs [sym, left_inverse RS ssubst]) 1);
val lemma4 = result();

Goal "[| n \\<in> nat; B \\<in> A; u(B) \\<subseteq> cons(0, B*nat); 0 \\<in> u(B); 2 lepoll u(B);  \
\       u(B) lepoll succ(n) |]  \
\       ==> (\\<lambda>x \\<in> A. {fst(x). x \\<in> u(x)-{0}})`B \\<noteq> 0 &  \
\               (\\<lambda>x \\<in> A. {fst(x). x \\<in> u(x)-{0}})`B \\<subseteq> B &  \
\               (\\<lambda>x \\<in> A. {fst(x). x \\<in> u(x)-{0}})`B lepoll n";
by (Asm_simp_tac 1);
by (rtac conjI 1);
by (fast_tac (empty_cs addSDs [RepFun_eq_0_iff RS iffD1]
                addDs [lepoll_Diff_sing]
                addEs [lepoll_trans RS succ_lepoll_natE, ssubst]
                addSIs [notI, lepoll_refl, nat_0I]) 1);
by (rtac conjI 1);
by (fast_tac (claset() addSIs [fst_type] addSEs [consE]) 1);
by (fast_tac (claset() addSEs [equalityE,
                Diff_lepoll RS (nat_into_Ord RSN (2, lemma4))]) 1);
val lemma5 = result();

Goal "[| \\<exists>f. \\<forall>B \\<in> {cons(0, x*nat). x \\<in> A}.  \
\               pairwise_disjoint(f`B) &  \
\               sets_of_size_between(f`B, 2, succ(n)) &  \
\               Union(f`B)=B; n \\<in> nat |]  \
\       ==> \\<exists>f. \\<forall>B \\<in> A. f`B \\<noteq> 0 & f`B \\<subseteq> B & f`B lepoll n";
by (fast_tac (empty_cs addSDs [lemma3, theI] addDs [bspec]
                addSEs [exE, conjE]
                addIs [exI, ballI, lemma5]) 1);
qed "ex_fun_AC13_AC15";

(* ********************************************************************** *)
(* The target proofs                                                      *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC10(n) ==> AC11                                                       *)
(* ********************************************************************** *)

Goalw AC_defs "[| n \\<in> nat; 1 le n; AC10(n) |] ==> AC11";
by (rtac bexI 1 THEN (assume_tac 2));
by (Fast_tac 1);
qed "AC10_AC11";

(* ********************************************************************** *)
(* AC11 ==> AC12                                                          *)
(* ********************************************************************** *)

Goalw AC_defs "AC11 ==> AC12";
by (fast_tac (FOL_cs addSEs [bexE] addIs [bexI]) 1);
qed "AC11_AC12";

(* ********************************************************************** *)
(* AC12 ==> AC15                                                          *)
(* ********************************************************************** *)

Goalw AC_defs "AC12 ==> AC15";
by Safe_tac;
by (etac allE 1);
by (etac impE 1);
by (etac cons_times_nat_not_Finite 1);
by (fast_tac (claset() addSIs [ex_fun_AC13_AC15]) 1);
qed "AC12_AC15";

(* ********************************************************************** *)
(* AC15 ==> WO6                                                           *)
(* ********************************************************************** *)

Goal "Ord(x) ==> (\\<Union>a<x. F(a)) = (\\<Union>a \\<in> x. F(a))";
by (fast_tac (claset() addSIs [ltI] addSDs [ltD]) 1);
qed "OUN_eq_UN";

val [prem] = goal thy "\\<forall>x \\<in> Pow(A)-{0}. f`x\\<noteq>0 & f`x \\<subseteq> x & f`x lepoll m ==>  \
\       (\\<Union>i<LEAST x. HH(f,A,x)={A}. HH(f,A,i)) = A";
by (simp_tac (simpset() addsimps [Ord_Least RS OUN_eq_UN]) 1);
by (rtac equalityI 1);
by (fast_tac (claset() addSDs [less_Least_subset_x]) 1);
by (fast_tac (claset() addSDs [prem RS bspec]
                addSIs [f_subsets_imp_UN_HH_eq_x RS (Diff_eq_0_iff RS iffD1)]) 1);
val lemma1 = result();

val [prem] = goal thy "\\<forall>x \\<in> Pow(A)-{0}. f`x\\<noteq>0 & f`x \\<subseteq> x & f`x lepoll m ==>  \
\       \\<forall>x<LEAST x. HH(f,A,x)={A}. HH(f,A,x) lepoll m";
by (rtac oallI 1);
by (dresolve_tac [ltD RS less_Least_subset_x] 1);
by (ftac HH_subset_imp_eq 1);
by (etac ssubst 1);
by (fast_tac (claset() addIs [prem RS ballE]
                addSDs [HH_subset_x_imp_subset_Diff_UN RS not_emptyI2]) 1);
val lemma2 = result();

Goalw [AC15_def, WO6_def] "AC15 ==> WO6";
by (rtac allI 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (etac impE 1);
by (Fast_tac 1);
by (REPEAT (eresolve_tac [bexE,conjE,exE] 1));
by (rtac bexI 1 THEN (assume_tac 2));
by (rtac conjI 1 THEN (assume_tac 1));
by (res_inst_tac [("x","LEAST i. HH(f,A,i)={A}")] exI 1);
by (res_inst_tac [("x","\\<lambda>j \\<in> (LEAST i. HH(f,A,i)={A}). HH(f,A,j)")] exI 1);
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addSIs [Ord_Least, lam_type RS domain_of_fun]
                addSEs [less_Least_subset_x, lemma1, lemma2]) 1);
qed "AC15_WO6";


(* ********************************************************************** *)
(* The proof needed in the first case, not in the second                  *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC10(n) ==> AC13(n-1)  if 2 le n                                       *)
(*                                                                        *)
(* Because of the change to the formal definition of AC10(n) we prove     *)
(* the following obviously equivalent theorem \\<in>                           *)
(* AC10(n) implies AC13(n) for (1 le n)                                   *)
(* ********************************************************************** *)

Goalw AC_defs "[| n \\<in> nat; 1 le n; AC10(n) |] ==> AC13(n)";
by Safe_tac;
by (fast_tac (empty_cs addSEs [allE, cons_times_nat_not_Finite RSN (2, impE),
                                ex_fun_AC13_AC15]) 1);
qed "AC10_AC13";

(* ********************************************************************** *)
(* The proofs needed in the second case, not in the first                 *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC1 ==> AC13(1)                                                        *)
(* ********************************************************************** *)

Goalw AC_defs "AC1 ==> AC13(1)";
by (rtac allI 1);
by (etac allE 1);
by (rtac impI 1);
by (mp_tac 1);
by (etac exE 1);
by (res_inst_tac [("x","\\<lambda>x \\<in> A. {f`x}")] exI 1);
by (asm_simp_tac (simpset() addsimps
		  [singleton_eqpoll_1 RS eqpoll_imp_lepoll,
		   singletonI RS not_emptyI]) 1);
qed "AC1_AC13";

(* ********************************************************************** *)
(* AC13(m) ==> AC13(n) for m \\<subseteq> n                                         *)
(* ********************************************************************** *)

Goalw AC_defs "[| m le n; AC13(m) |] ==> AC13(n)";
by (dtac le_imp_lepoll 1);
by (fast_tac (claset() addSEs [lepoll_trans]) 1);
qed "AC13_mono";

(* ********************************************************************** *)
(* The proofs necessary for both cases                                    *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC13(n) ==> AC14  if 1 \\<subseteq> n                                            *)
(* ********************************************************************** *)

Goalw AC_defs "[| n \\<in> nat; 1 le n; AC13(n) |] ==> AC14";
by (fast_tac (FOL_cs addIs [bexI]) 1);
qed "AC13_AC14";

(* ********************************************************************** *)
(* AC14 ==> AC15                                                          *)
(* ********************************************************************** *)

Goalw AC_defs "AC14 ==> AC15";
by (Fast_tac 1);
qed "AC14_AC15";

(* ********************************************************************** *)
(* The redundant proofs; however cited by Rubin & Rubin                   *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC13(1) ==> AC1                                                        *)
(* ********************************************************************** *)

Goal "[| A\\<noteq>0; A lepoll 1 |] ==> \\<exists>a. A={a}";
by (fast_tac (claset() addSEs [not_emptyE, lepoll_1_is_sing]) 1);
qed "lemma_aux";

Goal "\\<forall>B \\<in> A. f(B)\\<noteq>0 & f(B)<=B & f(B) lepoll 1  \
\     ==> (\\<lambda>x \\<in> A. THE y. f(x)={y}) \\<in> (\\<Pi>X \\<in> A. X)";
by (rtac lam_type 1);
by (dtac bspec 1 THEN (assume_tac 1));
by (REPEAT (etac conjE 1));
by (eresolve_tac [lemma_aux RS exE] 1 THEN (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [the_element]) 1);
val lemma = result();

Goalw AC_defs "AC13(1) ==> AC1";
by (fast_tac (claset() addSEs [lemma]) 1);
qed "AC13_AC1";

(* ********************************************************************** *)
(* AC11 ==> AC14                                                          *)
(* ********************************************************************** *)

Goalw [AC11_def, AC14_def] "AC11 ==> AC14";
by (fast_tac (claset() addSIs [AC10_AC13]) 1);
qed "AC11_AC14";
