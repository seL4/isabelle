(*  Title:      ZF/Finite.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator; finite function space

prove X:Fin(A) ==> |X| < nat

prove:  b: Fin(A) ==> inj(b,b)<=surj(b,b)
*)

(*** Finite powerset operator ***)

Goalw Fin.defs "A<=B ==> Fin(A) <= Fin(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Fin.bnd_mono 1));
by (REPEAT (ares_tac (Pow_mono::basic_monos) 1));
qed "Fin_mono";

(* A : Fin(B) ==> A <= B *)
val FinD = Fin.dom_subset RS subsetD RS PowD;

(** Induction on finite sets **)

(*Discharging x~:y entails extra work*)
val major::prems = Goal
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
Goal "[| b: Fin(A);  c: Fin(A) |] ==> b Un c : Fin(A)";
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
Goal "b: Fin(A) ==> ALL z. z<=b --> z: Fin(A)";
by (etac Fin_induct 1);
by (simp_tac (simpset() addsimps [subset_empty_iff]) 1);
by (asm_simp_tac (simpset() addsimps subset_cons_iff::distrib_simps) 1);
by Safe_tac;
by (eres_inst_tac [("b","z")] (cons_Diff RS subst) 1);
by (Asm_simp_tac 1);
qed "Fin_subset_lemma";

Goal "[| c<=b;  b: Fin(A) |] ==> c: Fin(A)";
by (REPEAT (ares_tac [Fin_subset_lemma RS spec RS mp] 1));
qed "Fin_subset";

Goal "b: Fin(A) ==> b Int c : Fin(A)";
by (blast_tac (claset() addIs [Fin_subset]) 1);
qed "Fin_IntI1";

Goal "c: Fin(A) ==> b Int c : Fin(A)";
by (blast_tac (claset() addIs [Fin_subset]) 1);
qed "Fin_IntI2";

Addsimps[Fin_IntI1, Fin_IntI2];
AddIs[Fin_IntI1, Fin_IntI2];


val major::prems = Goal
    "[| c: Fin(A);  b: Fin(A);                                  \
\       P(b);                                                   \
\       !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS Fin_induct) 1);
by (stac Diff_cons 2);
by (ALLGOALS (asm_simp_tac (simpset() addsimps (prems@[cons_subset_iff, 
                                Diff_subset RS Fin_subset]))));
qed "Fin_0_induct_lemma";

val prems = Goal
    "[| b: Fin(A);                                              \
\       P(b);                                                   \
\       !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> P(0)";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (Fin_0_induct_lemma RS mp) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "Fin_0_induct";

(*Functions from a finite ordinal*)
Goal "n: nat ==> n->A <= Fin(nat*A)";
by (induct_tac "n" 1);
by (simp_tac (simpset() addsimps [subset_iff]) 1);
by (asm_simp_tac 
    (simpset() addsimps [succ_def, mem_not_refl RS cons_fun_eq]) 1);
by (fast_tac (claset() addSIs [Fin.consI]) 1);
qed "nat_fun_subset_Fin";


(*** Finite function space ***)

Goalw FiniteFun.defs
    "[| A<=C;  B<=D |] ==> A -||> B  <=  C -||> D";
by (rtac lfp_mono 1);
by (REPEAT (rtac FiniteFun.bnd_mono 1));
by (REPEAT (ares_tac (Fin_mono::Sigma_mono::basic_monos) 1));
qed "FiniteFun_mono";

Goal "A<=B ==> A -||> A  <=  B -||> B";
by (REPEAT (ares_tac [FiniteFun_mono] 1));
qed "FiniteFun_mono1";

Goal "h: A -||>B ==> h: domain(h) -> B";
by (etac FiniteFun.induct 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [fun_extend3]) 1);
qed "FiniteFun_is_fun";

Goal "h: A -||>B ==> domain(h) : Fin(A)";
by (etac FiniteFun.induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "FiniteFun_domain_Fin";

bind_thm ("FiniteFun_apply_type", FiniteFun_is_fun RS apply_type);

(*Every subset of a finite function is a finite function.*)
Goal "b: A-||>B ==> ALL z. z<=b --> z: A-||>B";
by (etac FiniteFun.induct 1);
by (simp_tac (simpset() addsimps subset_empty_iff::FiniteFun.intrs) 1);
by (asm_simp_tac (simpset() addsimps subset_cons_iff::distrib_simps) 1);
by Safe_tac;
by (eres_inst_tac [("b","z")] (cons_Diff RS subst) 1);
by (dtac (spec RS mp) 1 THEN assume_tac 1);
by (fast_tac (claset() addSIs FiniteFun.intrs) 1);
qed "FiniteFun_subset_lemma";

Goal "[| c<=b;  b: A-||>B |] ==> c: A-||>B";
by (REPEAT (ares_tac [FiniteFun_subset_lemma RS spec RS mp] 1));
qed "FiniteFun_subset";

(** Some further results by Sidi O. Ehmety **)

Goal "A:Fin(X) ==> ALL f. f:A->B --> f:A-||>B";
by (etac Fin.induct 1);
by (simp_tac (simpset() addsimps FiniteFun.intrs) 1);
by (Clarify_tac 1);
by (case_tac "a:b" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [cons_absorb]) 1);
by (subgoal_tac "restrict(f,b) : b -||> B" 1);
by (blast_tac (claset() addIs [restrict_type2]) 2);
by (stac fun_cons_restrict_eq 1 THEN assume_tac 1);
by (full_simp_tac (simpset() addsimps [restrict_def, lam_def]) 1);
by (blast_tac (claset() addIs [apply_funtype, impOfSubs FiniteFun_mono]
                              @FiniteFun.intrs) 1);
qed_spec_mp "fun_FiniteFunI";

Goal "A: Fin(X) ==> (lam x:A. b(x)) : A -||> {b(x). x:A}";
by (blast_tac (claset() addIs [fun_FiniteFunI, lam_funtype]) 1);
qed "lam_FiniteFun";

Goal "f : FiniteFun(A, {y:B. P(y)})  \
\     <-> f : FiniteFun(A,B) & (ALL x:domain(f). P(f`x))";
by Auto_tac;
by (blast_tac (claset() addIs [impOfSubs FiniteFun_mono]) 1);
by (blast_tac (claset() addDs [FiniteFun_is_fun]
                        addEs [Pair_mem_PiE]) 1);
by (res_inst_tac [("A1", "domain(f)")]
    (subset_refl RSN(2, FiniteFun_mono) RS subsetD) 1);
by (fast_tac (claset() addDs
		[FiniteFun_domain_Fin, Fin.dom_subset RS subsetD]) 1);
by (rtac fun_FiniteFunI 1);
by (etac FiniteFun_domain_Fin 1);
by (res_inst_tac [("B" , "range(f)")] fun_weaken_type 1);
by (ALLGOALS
    (blast_tac (claset() addDs
		[FiniteFun_is_fun, range_of_fun, range_type,
		 apply_equality])));
qed "FiniteFun_Collect_iff";
