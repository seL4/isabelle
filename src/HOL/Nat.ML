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
by (exhaust_tac "n" 1);
by (REPEAT (Blast_tac 1));
qed "not0_implies_Suc";

Goal "m<n ==> n ~= 0";
by (exhaust_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "gr_implies_not0";

Goal "(n ~= 0) = (0 < n)";
by (exhaust_tac "n" 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "neq0_conv";
AddIffs [neq0_conv];

Goal "(0 ~= n) = (0 < n)";
by (exhaust_tac "n" 1);
by (Auto_tac);
qed "zero_neq_conv";
AddIffs [zero_neq_conv];

(*This theorem is useful with blast_tac: (n=0 ==> False) ==> 0<n *)
bind_thm ("gr0I", [neq0_conv, notI] MRS iffD1);

Goal "(~(0 < n)) = (n=0)";
by (rtac iffI 1);
 by (etac swap 1);
 by (ALLGOALS Asm_full_simp_tac);
qed "not_gr0";
AddIffs [not_gr0];

qed_goalw "Least_Suc" thy [Least_nat_def]
 "!!P. [| ? n. P(Suc n); ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P(Suc m))"
 (fn _ => [
        rtac select_equality 1,
        fold_goals_tac [Least_nat_def],
        safe_tac (claset() addSEs [LeastI]),
        rename_tac "j" 1,
        exhaust_tac "j" 1,
        Blast_tac 1,
        blast_tac (claset() addDs [Suc_less_SucD, not_less_Least]) 1,
        rename_tac "k n" 1,
        exhaust_tac "k" 1,
        Blast_tac 1,
        hyp_subst_tac 1,
        rewtac Least_nat_def,
        rtac (select_equality RS arg_cong RS sym) 1,
        Safe_tac,
        dtac Suc_mono 1,
        Blast_tac 1,
        cut_facts_tac [less_linear] 1,
        Safe_tac,
        atac 2,
        Blast_tac 2,
        dtac Suc_mono 1,
        Blast_tac 1]);

qed_goal "nat_induct2" thy 
"[| P 0; P 1; !!k. P k ==> P (Suc (Suc k)) |] ==> P n" (fn prems => [
        cut_facts_tac prems 1,
        rtac less_induct 1,
        exhaust_tac "n" 1,
         hyp_subst_tac 1,
         atac 1,
        hyp_subst_tac 1,
        exhaust_tac "nat" 1,
         hyp_subst_tac 1,
         atac 1,
        hyp_subst_tac 1,
        resolve_tac prems 1,
        dtac spec 1,
        etac mp 1,
        rtac (lessI RS less_trans) 1,
        rtac (lessI RS Suc_mono) 1]);

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
