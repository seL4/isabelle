(*  Title:      HOL/NatSimprocs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Simprocs for nat numerals (see also nat_simprocs.ML).
*)

(** For simplifying  Suc m - #n **)

Goal "#0 < n ==> Suc m - n = m - (n - #1)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "Suc_diff_eq_diff_pred";

(*Now just instantiating n to (number_of v) does the right simplification,
  but with some redundant inequality tests.*)

Goal "neg (number_of (bin_pred v)) = (number_of v = (0::nat))";
by (subgoal_tac "neg (number_of (bin_pred v)) = (number_of v < 1)" 1);
by (Asm_simp_tac 1);
by (stac less_number_of_Suc 1);
by (Simp_tac 1);
qed "neg_number_of_bin_pred_iff_0";

Goal "neg (number_of (bin_minus v)) ==> \
\     Suc m - (number_of v) = m - (number_of (bin_pred v))";
by (stac Suc_diff_eq_diff_pred 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (asm_full_simp_tac
    (simpset_of Int.thy addsimps [diff_nat_number_of, less_0_number_of RS sym,
                                  neg_number_of_bin_pred_iff_0]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset_of Int.thy) 1);
qed "Suc_diff_number_of";

(* now redundant because of the inverse_fold simproc
    Addsimps [Suc_diff_number_of]; *)

Goal "nat_case a f (number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then a else f (nat pv))";
by (simp_tac
    (simpset() addsplits [nat.split]
                        addsimps [Let_def, neg_number_of_bin_pred_iff_0]) 1);
qed "nat_case_number_of";

Goal "nat_case a f ((number_of v) + n) = \
\      (let pv = number_of (bin_pred v) in \
\        if neg pv then nat_case a f n else f (nat pv + n))";
by (stac add_eq_if 1);
by (asm_simp_tac
    (simpset() addsplits [nat.split]
               addsimps [Let_def, neg_imp_number_of_eq_0,
                         neg_number_of_bin_pred_iff_0]) 1);
qed "nat_case_add_eq_if";

Addsimps [nat_case_number_of, nat_case_add_eq_if];


Goal "nat_rec a f (number_of v) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then a else f (nat pv) (nat_rec a f (nat pv)))";
by (case_tac "(number_of v)::nat" 1);
by (ALLGOALS (asm_simp_tac
              (simpset() addsimps [Let_def, neg_number_of_bin_pred_iff_0])));
by (asm_full_simp_tac (simpset() addsplits [split_if_asm]) 1);
qed "nat_rec_number_of";

Goal "nat_rec a f (number_of v + n) = \
\       (let pv = number_of (bin_pred v) in \
\        if neg pv then nat_rec a f n \
\                  else f (nat pv + n) (nat_rec a f (nat pv + n)))";
by (stac add_eq_if 1);
by (asm_simp_tac
    (simpset() addsplits [nat.split]
               addsimps [Let_def, neg_imp_number_of_eq_0,
                         neg_number_of_bin_pred_iff_0]) 1);
qed "nat_rec_add_eq_if";

Addsimps [nat_rec_number_of, nat_rec_add_eq_if];


(** For simplifying  #m - Suc n **)

Goal "m - Suc n = (m - #1) - n";
by (simp_tac (numeral_ss addsplits [nat_diff_split]) 1);
qed "diff_Suc_eq_diff_pred";

(*Obsolete because of natdiff_cancel_numerals
    Addsimps [inst "m" "number_of ?v" diff_Suc_eq_diff_pred];
  It LOOPS if #1 is being replaced by 1.
*)


(** Evens and Odds, for Mutilated Chess Board **)

(*Case analysis on b<#2*)
Goal "(n::nat) < #2 ==> n = #0 | n = #1";
by (arith_tac 1);
qed "less_2_cases";

Goal "Suc(Suc(m)) mod #2 = m mod #2";
by (subgoal_tac "m mod #2 < #2" 1);
by (Asm_simp_tac 2);
be (less_2_cases RS disjE) 1;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mod_Suc])));
qed "mod2_Suc_Suc";
Addsimps [mod2_Suc_Suc];

Goal "!!m::nat. (0 < m mod #2) = (m mod #2 = #1)";
by (subgoal_tac "m mod #2 < #2" 1);
by (Asm_simp_tac 2);
by (auto_tac (claset(), simpset() delsimps [mod_less_divisor]));
qed "mod2_gr_0";
Addsimps [mod2_gr_0, rename_numerals mod2_gr_0];

(** Removal of small numerals: #0, #1 and (in additive positions) #2 **)

Goal "#2 + n = Suc (Suc n)";
by (Simp_tac 1);
qed "add_2_eq_Suc";

Goal "n + #2 = Suc (Suc n)";
by (Simp_tac 1);
qed "add_2_eq_Suc'";

Addsimps [numeral_0_eq_0, numeral_1_eq_1, add_2_eq_Suc, add_2_eq_Suc'];

(*Can be used to eliminate long strings of Sucs, but not by default*)
Goal "Suc (Suc (Suc n)) = #3 + n";
by (Simp_tac 1);
qed "Suc3_eq_add_3";


(** To collapse some needless occurrences of Suc 
    At least three Sucs, since two and fewer are rewritten back to Suc again!

    We already have some rules to simplify operands smaller than 3.
**)

Goal "m div (Suc (Suc (Suc n))) = m div (#3+n)";
by (simp_tac (simpset() addsimps [Suc3_eq_add_3]) 1);
qed "div_Suc_eq_div_add3";

Goal "m mod (Suc (Suc (Suc n))) = m mod (#3+n)";
by (simp_tac (simpset() addsimps [Suc3_eq_add_3]) 1);
qed "mod_Suc_eq_mod_add3";

Addsimps [div_Suc_eq_div_add3, mod_Suc_eq_mod_add3];

Goal "(Suc (Suc (Suc m))) div n = (#3+m) div n";
by (simp_tac (simpset() addsimps [Suc3_eq_add_3]) 1);
qed "Suc_div_eq_add3_div";

Goal "(Suc (Suc (Suc m))) mod n = (#3+m) mod n";
by (simp_tac (simpset() addsimps [Suc3_eq_add_3]) 1);
qed "Suc_mod_eq_add3_mod";

Addsimps [inst "n" "number_of ?v" Suc_div_eq_add3_div,
	  inst "n" "number_of ?v" Suc_mod_eq_add3_mod];
