(*  Title:      HOL/NatSimprocs.thy
    ID:         $Id$
    Copyright   2003 TU Muenchen
*)

header {*Simprocs for the Naturals*}

theory NatSimprocs = NatBin
files "int_factor_simprocs.ML" "nat_simprocs.ML":

setup nat_simprocs_setup

subsection{*For simplifying @{term "Suc m - K"} and  @{term "K - Suc m"}*}

text{*Where K above is a literal*}

lemma Suc_diff_eq_diff_pred: "Numeral0 < n ==> Suc m - n = m - (n - Numeral1)"
by (simp add: numeral_0_eq_0 numeral_1_eq_1 split add: nat_diff_split)

(*Now just instantiating n to (number_of v) does the right simplification,
  but with some redundant inequality tests.*)
lemma neg_number_of_bin_pred_iff_0:
     "neg (number_of (bin_pred v)) = (number_of v = (0::nat))"
apply (subgoal_tac "neg (number_of (bin_pred v)) = (number_of v < Suc 0) ")
apply (simp only: less_Suc_eq_le le_0_eq)
apply (subst less_number_of_Suc, simp)
done

text{*No longer required as a simprule because of the @{text inverse_fold}
   simproc*}
lemma Suc_diff_number_of:
     "neg (number_of (bin_minus v)) ==>  
      Suc m - (number_of v) = m - (number_of (bin_pred v))"
apply (subst Suc_diff_eq_diff_pred, simp, simp)
apply (force simp only: diff_nat_number_of less_0_number_of [symmetric] 
                        neg_number_of_bin_pred_iff_0)
done

lemma diff_Suc_eq_diff_pred: "m - Suc n = (m - 1) - n"
by (simp add: numerals split add: nat_diff_split)


subsection{*For @{term nat_case} and @{term nat_rec}*}

lemma nat_case_number_of [simp]:
     "nat_case a f (number_of v) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then a else f (nat pv))"
by (simp split add: nat.split add: Let_def neg_number_of_bin_pred_iff_0)

lemma nat_case_add_eq_if [simp]:
     "nat_case a f ((number_of v) + n) =  
       (let pv = number_of (bin_pred v) in  
         if neg pv then nat_case a f n else f (nat pv + n))"
apply (subst add_eq_if)
apply (simp split add: nat.split
            add: numeral_1_eq_Suc_0 [symmetric] Let_def 
                 neg_imp_number_of_eq_0 neg_number_of_bin_pred_iff_0)
done

lemma nat_rec_number_of [simp]:
     "nat_rec a f (number_of v) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then a else f (nat pv) (nat_rec a f (nat pv)))"
apply (case_tac " (number_of v) ::nat")
apply (simp_all (no_asm_simp) add: Let_def neg_number_of_bin_pred_iff_0)
apply (simp split add: split_if_asm)
done

lemma nat_rec_add_eq_if [simp]:
     "nat_rec a f (number_of v + n) =  
        (let pv = number_of (bin_pred v) in  
         if neg pv then nat_rec a f n  
                   else f (nat pv + n) (nat_rec a f (nat pv + n)))"
apply (subst add_eq_if)
apply (simp split add: nat.split
            add: numeral_1_eq_Suc_0 [symmetric] Let_def neg_imp_number_of_eq_0
                 neg_number_of_bin_pred_iff_0)
done


subsection{*Various Other Lemmas*}

subsubsection{*Evens and Odds, for Mutilated Chess Board*}

(*Case analysis on b<2*)
lemma less_2_cases: "(n::nat) < 2 ==> n = 0 | n = Suc 0"
by arith

lemma mod2_Suc_Suc [simp]: "Suc(Suc(m)) mod 2 = m mod 2"
apply (subgoal_tac "m mod 2 < 2")
apply (erule less_2_cases [THEN disjE])
apply (simp_all (no_asm_simp) add: Let_def mod_Suc nat_1)
done

lemma mod2_gr_0 [simp]: "!!m::nat. (0 < m mod 2) = (m mod 2 = 1)"
apply (subgoal_tac "m mod 2 < 2")
apply (force simp del: mod_less_divisor, simp) 
done

subsubsection{*Removal of Small Numerals: 0, 1 and (in additive positions) 2*}

lemma add_2_eq_Suc [simp]: "2 + n = Suc (Suc n)"
by simp

lemma add_2_eq_Suc' [simp]: "n + 2 = Suc (Suc n)"
by simp

declare numeral_0_eq_0 [simp] numeral_1_eq_1 [simp] 

text{*Can be used to eliminate long strings of Sucs, but not by default*}
lemma Suc3_eq_add_3: "Suc (Suc (Suc n)) = 3 + n"
by simp


text{*These lemmas collapse some needless occurrences of Suc:
    at least three Sucs, since two and fewer are rewritten back to Suc again!
    We already have some rules to simplify operands smaller than 3.*}

lemma div_Suc_eq_div_add3 [simp]: "m div (Suc (Suc (Suc n))) = m div (3+n)"
by (simp add: Suc3_eq_add_3)

lemma mod_Suc_eq_mod_add3 [simp]: "m mod (Suc (Suc (Suc n))) = m mod (3+n)"
by (simp add: Suc3_eq_add_3)

lemma Suc_div_eq_add3_div: "(Suc (Suc (Suc m))) div n = (3+m) div n"
by (simp add: Suc3_eq_add_3)

lemma Suc_mod_eq_add3_mod: "(Suc (Suc (Suc m))) mod n = (3+m) mod n"
by (simp add: Suc3_eq_add_3)

declare Suc_div_eq_add3_div [of _ "number_of v", standard, simp]
declare Suc_mod_eq_add3_mod [of _ "number_of v", standard, simp]


subsection{*Special Simplification for Constants*}

text{*These belong here, late in the development of HOL, to prevent their
interfering with proofs of abstract properties of instances of the function
@{term number_of}*}

text{*These distributive laws move literals inside sums and differences.*}
declare left_distrib [of _ _ "number_of v", standard, simp]
declare right_distrib [of "number_of v", standard, simp]

declare left_diff_distrib [of _ _ "number_of v", standard, simp]
declare right_diff_distrib [of "number_of v", standard, simp]

text{*These are actually for fields, like real: but where else to put them?*}
declare zero_less_divide_iff [of "number_of w", standard, simp]
declare divide_less_0_iff [of "number_of w", standard, simp]
declare zero_le_divide_iff [of "number_of w", standard, simp]
declare divide_le_0_iff [of "number_of w", standard, simp]

(*Replaces "inverse #nn" by 1/#nn *)
declare inverse_eq_divide [of "number_of w", standard, simp]

text{*These laws simplify inequalities, moving unary minus from a term
into the literal.*}
declare less_minus_iff [of "number_of v", standard, simp]
declare le_minus_iff [of "number_of v", standard, simp]
declare equation_minus_iff [of "number_of v", standard, simp]

declare minus_less_iff [of _ "number_of v", standard, simp]
declare minus_le_iff [of _ "number_of v", standard, simp]
declare minus_equation_iff [of _ "number_of v", standard, simp]

text{*These simplify inequalities where one side is the constant 1.*}
declare less_minus_iff [of 1, simplified, simp]
declare le_minus_iff [of 1, simplified, simp]
declare equation_minus_iff [of 1, simplified, simp]

declare minus_less_iff [of _ 1, simplified, simp]
declare minus_le_iff [of _ 1, simplified, simp]
declare minus_equation_iff [of _ 1, simplified, simp]


(*Cancellation of constant factors in comparisons (< and \<le>) *)

declare mult_less_cancel_left [of "number_of v", standard, simp]
declare mult_less_cancel_right [of _ "number_of v", standard, simp]
declare mult_le_cancel_left [of "number_of v", standard, simp]
declare mult_le_cancel_right [of _ "number_of v", standard, simp]


(*Multiplying out constant divisors in comparisons (< \<le> and =) *)

declare le_divide_eq [of _ _ "number_of w", standard, simp]
declare divide_le_eq [of _ "number_of w", standard, simp]
declare less_divide_eq [of _ _ "number_of w", standard, simp]
declare divide_less_eq [of _ "number_of w", standard, simp]
declare eq_divide_eq [of _ _ "number_of w", standard, simp]
declare divide_eq_eq [of _ "number_of w", standard, simp]


end
