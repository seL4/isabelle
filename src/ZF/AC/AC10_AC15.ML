(*  Title:      ZF/AC/AC10_AC15.ML
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

goalw thy [lepoll_def] "!!A. A~=0 ==> B lepoll A*B";
by (etac not_emptyE 1);
by (res_inst_tac [("x","lam z:B. <x,z>")] exI 1);
by (fast_tac (!claset addSIs [snd_conv, lam_injective]) 1);
val lepoll_Sigma = result();

goal thy "!!A. 0~:A ==> ALL B:{cons(0,x*nat). x:A}. ~Finite(B)";
by (rtac ballI 1);
by (etac RepFunE 1);
by (hyp_subst_tac 1);
by (rtac notI 1);
by (dresolve_tac [subset_consI RS subset_imp_lepoll RS lepoll_Finite] 1);
by (resolve_tac [lepoll_Sigma RS lepoll_Finite RS (nat_not_Finite RS notE)] 1
        THEN (assume_tac 2));
by (Fast_tac 1);
val cons_times_nat_not_Finite = result();

goal thy "!!A. [| Union(C)=A; a:A |] ==> EX B:C. a:B & B <= A";
by (Fast_tac 1);
val lemma1 = result();

goalw thy [pairwise_disjoint_def]
        "!!A. [| pairwise_disjoint(A); B:A; C:A; a:B; a:C |] ==> B=C";
by (dtac IntI 1 THEN (assume_tac 1));
by (dres_inst_tac [("A","B Int C")] not_emptyI 1);
by (Fast_tac 1);
val lemma2 = result();

goalw thy [sets_of_size_between_def]
        "!!A. ALL B:{cons(0, x*nat). x:A}. pairwise_disjoint(f`B) &  \
\               sets_of_size_between(f`B, 2, n) & Union(f`B)=B  \
\       ==> ALL B:A. EX! u. u:f`cons(0, B*nat) & u <= cons(0, B*nat) &  \
\               0:u & 2 lepoll u & u lepoll n";
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

goalw thy [lepoll_def] "!!A. [| A lepoll i; Ord(i) |] ==> {P(a). a:A} lepoll i";
by (etac exE 1);
by (res_inst_tac
        [("x", "lam x:RepFun(A, P). LEAST j. EX a:A. x=P(a) & f`a=j")] exI 1);
by (res_inst_tac [("d", "%y. P(converse(f)`y)")] lam_injective 1);
by (etac RepFunE 1);
by (forward_tac [inj_is_fun RS apply_type] 1 THEN (assume_tac 1));
by (fast_tac (!claset addIs [LeastI2]
                addSEs [Ord_in_Ord, inj_is_fun RS apply_type]) 1);
by (etac RepFunE 1);
by (rtac LeastI2 1);
by (Fast_tac 1);
by (fast_tac (!claset addSEs [Ord_in_Ord, inj_is_fun RS apply_type]) 1);
by (fast_tac (!claset addEs [sym, left_inverse RS ssubst]) 1);
val lemma4 = result();

goal thy "!!A. [| n:nat; B:A; u(B) <= cons(0, B*nat); 0:u(B); 2 lepoll u(B);  \
\       u(B) lepoll succ(n) |]  \
\       ==> (lam x:A. {fst(x). x:u(x)-{0}})`B ~= 0 &  \
\               (lam x:A. {fst(x). x:u(x)-{0}})`B <= B &  \
\               (lam x:A. {fst(x). x:u(x)-{0}})`B lepoll n";
by (Asm_simp_tac 1);
by (rtac conjI 1);
by (fast_tac (empty_cs addSDs [RepFun_eq_0_iff RS iffD1]
                addDs [lepoll_Diff_sing]
                addEs [lepoll_trans RS succ_lepoll_natE, ssubst]
                addSIs [notI, lepoll_refl, nat_0I]) 1);
by (rtac conjI 1);
by (fast_tac (!claset addSIs [fst_type] addSEs [consE]) 1);
by (fast_tac (!claset addSEs [equalityE,
                Diff_lepoll RS (nat_into_Ord RSN (2, lemma4))]) 1);
val lemma5 = result();

goal thy "!!A. [| EX f. ALL B:{cons(0, x*nat). x:A}.  \
\               pairwise_disjoint(f`B) &  \
\               sets_of_size_between(f`B, 2, succ(n)) &  \
\               Union(f`B)=B; n:nat |]  \
\       ==> EX f. ALL B:A. f`B ~= 0 & f`B <= B & f`B lepoll n";
by (fast_tac (empty_cs addSDs [lemma3, theI] addDs [bspec]
                addSEs [exE, conjE]
                addIs [exI, ballI, lemma5]) 1);
val ex_fun_AC13_AC15 = result();

(* ********************************************************************** *)
(* The target proofs                                                      *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC10(n) ==> AC11                                                       *)
(* ********************************************************************** *)

goalw thy AC_defs "!!Z. [| n:nat; 1 le n; AC10(n) |] ==> AC11";
by (rtac bexI 1 THEN (assume_tac 2));
by (Fast_tac 1);
qed "AC10_AC11";

(* ********************************************************************** *)
(* AC11 ==> AC12                                                          *)
(* ********************************************************************** *)

goalw thy AC_defs "!! Z. AC11 ==> AC12";
by (fast_tac (FOL_cs addSEs [bexE] addIs [bexI]) 1);
qed "AC11_AC12";

(* ********************************************************************** *)
(* AC12 ==> AC15                                                          *)
(* ********************************************************************** *)

goalw thy AC_defs "!!Z. AC12 ==> AC15";
by (safe_tac (!claset));
by (etac allE 1);
by (etac impE 1);
by (etac cons_times_nat_not_Finite 1);
by (fast_tac (!claset addSIs [ex_fun_AC13_AC15]) 1);
qed "AC12_AC15";

(* ********************************************************************** *)
(* AC15 ==> WO6                                                           *)
(* ********************************************************************** *)

(* in a separate file *)

(* ********************************************************************** *)
(* The proof needed in the first case, not in the second                  *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC10(n) ==> AC13(n-1)  if 2 le n                                       *)
(*                                                                        *)
(* Because of the change to the formal definition of AC10(n) we prove     *)
(* the following obviously equivalent theorem :                           *)
(* AC10(n) implies AC13(n) for (1 le n)                                   *)
(* ********************************************************************** *)

goalw thy AC_defs "!!n. [| n:nat; 1 le n; AC10(n) |] ==> AC13(n)";
by (safe_tac (!claset));
by (fast_tac (empty_cs addSEs [allE, cons_times_nat_not_Finite RSN (2, impE),
                                ex_fun_AC13_AC15]) 1);
qed "AC10_AC13";

(* ********************************************************************** *)
(* The proofs needed in the second case, not in the first                 *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC1 ==> AC13(1)                                                        *)
(* ********************************************************************** *)

goalw thy AC_defs "!!Z. AC1 ==> AC13(1)";
by (rtac allI 1);
by (etac allE 1);
by (rtac impI 1);
by (mp_tac 1);
by (etac exE 1);
by (res_inst_tac [("x","lam x:A. {f`x}")] exI 1);
by (asm_full_simp_tac (!simpset addsimps
                [singleton_eqpoll_1 RS eqpoll_imp_lepoll,
                singletonI RS not_emptyI]) 1);
by (fast_tac (!claset addSEs [apply_type]) 1);
qed "AC1_AC13";

(* ********************************************************************** *)
(* AC13(m) ==> AC13(n) for m <= n                                         *)
(* ********************************************************************** *)

goalw thy AC_defs "!!m n. [| m:nat; n:nat; m le n; AC13(m) |] ==> AC13(n)";
by (dtac nat_le_imp_lepoll 1 THEN REPEAT (assume_tac 1));
by (fast_tac (!claset addSEs [lepoll_trans]) 1);
qed "AC13_mono";

(* ********************************************************************** *)
(* The proofs necessary for both cases                                    *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC13(n) ==> AC14  if 1 <= n                                            *)
(* ********************************************************************** *)

goalw thy AC_defs "!!n. [| n:nat; 1 le n; AC13(n) |] ==> AC14";
by (fast_tac (FOL_cs addIs [bexI]) 1);
qed "AC13_AC14";

(* ********************************************************************** *)
(* AC14 ==> AC15                                                          *)
(* ********************************************************************** *)

goalw thy AC_defs "!!Z. AC14 ==> AC15";
by (Fast_tac 1);
qed "AC14_AC15";

(* ********************************************************************** *)
(* The redundant proofs; however cited by Rubin & Rubin                   *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC13(1) ==> AC1                                                        *)
(* ********************************************************************** *)

goal thy "!!A. [| A~=0; A lepoll 1 |] ==> EX a. A={a}";
by (fast_tac (!claset addSEs [not_emptyE, lepoll_1_is_sing]) 1);
val lemma_aux = result();

goal thy "!!f. ALL B:A. f(B)~=0 & f(B)<=B & f(B) lepoll 1  \
\               ==> (lam x:A. THE y. f(x)={y}) : (PROD X:A. X)";
by (rtac lam_type 1);
by (dtac bspec 1 THEN (assume_tac 1));
by (REPEAT (etac conjE 1));
by (eresolve_tac [lemma_aux RS exE] 1 THEN (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [the_element]) 1);
by (fast_tac (!claset addEs [ssubst]) 1);
val lemma = result();

goalw thy AC_defs "!!Z. AC13(1) ==> AC1";
by (fast_tac (!claset addSEs [lemma]) 1);
qed "AC13_AC1";

(* ********************************************************************** *)
(* AC11 ==> AC14                                                          *)
(* ********************************************************************** *)

goalw thy [AC11_def, AC14_def] "!!Z. AC11 ==> AC14";
by (fast_tac (!claset addSIs [AC10_AC13]) 1);
qed "AC11_AC14";
