(*  Title:      HOL/Nat.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen
*)

(** conversion rules for nat_rec **)

val [nat_rec_0, nat_rec_Suc] = nat.recs;

(*These 2 rules ease the use of primitive recursion.  NOTE USE OF == *)
val prems = Goal
    "[| !!n. f(n) == nat_rec c h n |] ==> f(0) = c";
by (simp_tac (simpset() addsimps prems) 1);
qed "def_nat_rec_0";

val prems = Goal
    "[| !!n. f(n) == nat_rec c h n |] ==> f(Suc(n)) = h n (f n)";
by (simp_tac (simpset() addsimps prems) 1);
qed "def_nat_rec_Suc";

val [nat_case_0, nat_case_Suc] = nat.cases;

Goal "n ~= 0 ==> EX m. n = Suc m";
by (cases_tac "n" 1);
by (REPEAT (Blast_tac 1));
qed "not0_implies_Suc";

Goal "m<n ==> n ~= 0";
by (cases_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "gr_implies_not0";

Goal "(n ~= 0) = (0 < n)";
by (cases_tac "n" 1);
by Auto_tac;
qed "neq0_conv";
AddIffs [neq0_conv];

Goal "(0 ~= n) = (0 < n)";
by (cases_tac "n" 1);
by Auto_tac;
qed "zero_neq_conv";
AddIffs [zero_neq_conv];

(*This theorem is useful with blast_tac: (n=0 ==> False) ==> 0<n *)
bind_thm ("gr0I", [neq0_conv, notI] MRS iffD1);

Goal "(0<n) = (EX m. n = Suc m)";
by(fast_tac (claset() addIs [not0_implies_Suc]) 1);
qed "gr0_conv_Suc";

Goal "(~(0 < n)) = (n=0)";
by (rtac iffI 1);
 by (etac swap 1);
 by (ALLGOALS Asm_full_simp_tac);
qed "not_gr0";
AddIffs [not_gr0];

Goal "(Suc n <= m') --> (? m. m' = Suc m)";
by (induct_tac "m'" 1);
by  Auto_tac;
qed_spec_mp "Suc_le_D";

(*Useful in certain inductive arguments*)
Goal "(m < Suc n) = (m=0 | (EX j. m = Suc j & j < n))";
by (cases_tac "m" 1);
by Auto_tac;
qed "less_Suc_eq_0_disj";

Goalw [Least_nat_def]
 "[| ? n. P(Suc n); ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P(Suc m))";
by (rtac select_equality 1);
by (fold_goals_tac [Least_nat_def]);
by (safe_tac (claset() addSEs [LeastI]));
by (rename_tac "j" 1);
by (cases_tac "j" 1);
by (Blast_tac 1);
by (blast_tac (claset() addDs [Suc_less_SucD, not_less_Least]) 1);
by (rename_tac "k n" 1);
by (cases_tac "k" 1);
by (Blast_tac 1);
by (hyp_subst_tac 1);
by (rewtac Least_nat_def);
by (rtac (select_equality RS arg_cong RS sym) 1);
by (blast_tac (claset() addDs [Suc_mono]) 1);
by (cut_inst_tac [("m","m")] less_linear 1);
by (blast_tac (claset() addIs [Suc_mono]) 1);
qed "Least_Suc";

val prems = Goal "[| P 0; P 1; !!k. P k ==> P (Suc (Suc k)) |] ==> P n";
by (rtac less_induct 1);
by (cases_tac "n" 1);
by (cases_tac "nat" 2);
by (ALLGOALS (blast_tac (claset() addIs prems@[less_trans])));
qed "nat_induct2";

Goal "min 0 n = 0";
by (rtac min_leastL 1);
by (Simp_tac 1);
qed "min_0L";

Goal "min n 0 = 0";
by (rtac min_leastR 1);
by (Simp_tac 1);
qed "min_0R";

Goalw [min_def] "min (Suc m) (Suc n) = Suc(min m n)";
by (Simp_tac 1);
qed "min_Suc_Suc";

Addsimps [min_0L,min_0R,min_Suc_Suc];

Goalw [max_def] "max 0 n = n";
by (Simp_tac 1);
qed "max_0L";

Goalw [max_def] "max n 0 = n";
by (Simp_tac 1);
qed "max_0R";

Goalw [max_def] "max (Suc m) (Suc n) = Suc(max m n)";
by (Simp_tac 1);
qed "max_Suc_Suc";

Addsimps [max_0L,max_0R,max_Suc_Suc];
