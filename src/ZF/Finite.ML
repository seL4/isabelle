(*  Title:      ZF/Finite.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator; finite function space

prove X:Fin(A) ==> |X| < nat

prove:  b: Fin(A) ==> inj(b,b)<=surj(b,b)
*)

open Finite;

(*** Finite powerset operator ***)

goalw Finite.thy Fin.defs "!!A B. A<=B ==> Fin(A) <= Fin(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Fin.bnd_mono 1));
by (REPEAT (ares_tac (Pow_mono::basic_monos) 1));
qed "Fin_mono";

(* A : Fin(B) ==> A <= B *)
val FinD = Fin.dom_subset RS subsetD RS PowD;

(** Induction on finite sets **)

(*Discharging x~:y entails extra work*)
val major::prems = goal Finite.thy 
    "[| b: Fin(A);  \
\       P(0);        \
\       !!x y. [| x: A;  y: Fin(A);  x~:y;  P(y) |] ==> P(cons(x,y)) \
\    |] ==> P(b)";
by (rtac (major RS Fin.induct) 1);
by (excluded_middle_tac "a:b" 2);
by (etac (cons_absorb RS ssubst) 3 THEN assume_tac 3);      (*backtracking!*)
by (REPEAT (ares_tac prems 1));
qed "Fin_induct";

(** Simplification for Fin **)
Addsimps Fin.intrs;

(*The union of two finite sets is finite.*)
goal Finite.thy
    "!!b c. [| b: Fin(A);  c: Fin(A) |] ==> b Un c : Fin(A)";
by (etac Fin_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Un_cons])));
qed "Fin_UnI";

Addsimps [Fin_UnI];

(*The union of a set of finite sets is finite.*)
val [major] = goal Finite.thy "C : Fin(Fin(A)) ==> Union(C) : Fin(A)";
by (rtac (major RS Fin_induct) 1);
by (ALLGOALS Asm_simp_tac);
qed "Fin_UnionI";

(*Every subset of a finite set is finite.*)
goal Finite.thy "!!b A. b: Fin(A) ==> ALL z. z<=b --> z: Fin(A)";
by (etac Fin_induct 1);
by (simp_tac (simpset() addsimps [subset_empty_iff]) 1);
by (asm_simp_tac (simpset() addsimps subset_cons_iff::distrib_simps) 1);
by (safe_tac (claset()));
by (eres_inst_tac [("b","z")] (cons_Diff RS subst) 1);
by (Asm_simp_tac 1);
qed "Fin_subset_lemma";

goal Finite.thy "!!c b A. [| c<=b;  b: Fin(A) |] ==> c: Fin(A)";
by (REPEAT (ares_tac [Fin_subset_lemma RS spec RS mp] 1));
qed "Fin_subset";

val major::prems = goal Finite.thy 
    "[| c: Fin(A);  b: Fin(A);                                  \
\       P(b);                                                   \
\       !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS Fin_induct) 1);
by (stac Diff_cons 2);
by (ALLGOALS (asm_simp_tac (simpset() addsimps (prems@[cons_subset_iff, 
                                Diff_subset RS Fin_subset]))));
qed "Fin_0_induct_lemma";

val prems = goal Finite.thy 
    "[| b: Fin(A);                                              \
\       P(b);                                                   \
\       !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> P(0)";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (Fin_0_induct_lemma RS mp) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "Fin_0_induct";

(*Functions from a finite ordinal*)
val prems = goal Finite.thy "n: nat ==> n->A <= Fin(nat*A)";
by (nat_ind_tac "n" prems 1);
by (simp_tac (simpset() addsimps [Pi_empty1, subset_iff, cons_iff]) 1);
by (asm_simp_tac (simpset() addsimps [succ_def, mem_not_refl RS cons_fun_eq]) 1);
by (fast_tac (claset() addSIs [Fin.consI]) 1);
qed "nat_fun_subset_Fin";


(*** Finite function space ***)

goalw Finite.thy FiniteFun.defs
    "!!A B C D. [| A<=C;  B<=D |] ==> A -||> B  <=  C -||> D";
by (rtac lfp_mono 1);
by (REPEAT (rtac FiniteFun.bnd_mono 1));
by (REPEAT (ares_tac (Fin_mono::Sigma_mono::basic_monos) 1));
qed "FiniteFun_mono";

goal Finite.thy "!!A B. A<=B ==> A -||> A  <=  B -||> B";
by (REPEAT (ares_tac [FiniteFun_mono] 1));
qed "FiniteFun_mono1";

goal Finite.thy "!!h. h: A -||>B ==> h: domain(h) -> B";
by (etac FiniteFun.induct 1);
by (simp_tac (simpset() addsimps [empty_fun, domain_0]) 1);
by (asm_simp_tac (simpset() addsimps [fun_extend3, domain_cons]) 1);
qed "FiniteFun_is_fun";

goal Finite.thy "!!h. h: A -||>B ==> domain(h) : Fin(A)";
by (etac FiniteFun.induct 1);
by (simp_tac (simpset() addsimps [domain_0]) 1);
by (asm_simp_tac (simpset() addsimps [domain_cons]) 1);
qed "FiniteFun_domain_Fin";

bind_thm ("FiniteFun_apply_type", FiniteFun_is_fun RS apply_type);

(*Every subset of a finite function is a finite function.*)
goal Finite.thy "!!b A. b: A-||>B ==> ALL z. z<=b --> z: A-||>B";
by (etac FiniteFun.induct 1);
by (simp_tac (simpset() addsimps subset_empty_iff::FiniteFun.intrs) 1);
by (asm_simp_tac (simpset() addsimps subset_cons_iff::distrib_simps) 1);
by (safe_tac (claset()));
by (eres_inst_tac [("b","z")] (cons_Diff RS subst) 1);
by (dtac (spec RS mp) 1 THEN assume_tac 1);
by (fast_tac (claset() addSIs FiniteFun.intrs) 1);
qed "FiniteFun_subset_lemma";

goal Finite.thy "!!c b A. [| c<=b;  b: A-||>B |] ==> c: A-||>B";
by (REPEAT (ares_tac [FiniteFun_subset_lemma RS spec RS mp] 1));
qed "FiniteFun_subset";

