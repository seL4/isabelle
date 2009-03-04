(*  Title:      HOL/Arith_Tools.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Setup of arithmetic tools *}

theory Arith_Tools
imports NatBin
uses
  "~~/src/Provers/Arith/cancel_numeral_factor.ML"
  "~~/src/Provers/Arith/extract_common_term.ML"
  "Tools/int_factor_simprocs.ML"
  "Tools/nat_simprocs.ML"
  "Tools/Qelim/qelim.ML"
begin

subsection {* Simprocs for the Naturals *}

declaration {* K nat_simprocs_setup *}

subsubsection{*For simplifying @{term "Suc m - K"} and  @{term "K - Suc m"}*}

text{*Where K above is a literal*}

lemma Suc_diff_eq_diff_pred: "Numeral0 < n ==> Suc m - n = m - (n - Numeral1)"
by (simp add: numeral_0_eq_0 numeral_1_eq_1 split add: nat_diff_split)

text {*Now just instantiating @{text n} to @{text "number_of v"} does
  the right simplification, but with some redundant inequality
  tests.*}
lemma neg_number_of_pred_iff_0:
  "neg (number_of (Int.pred v)::int) = (number_of v = (0::nat))"
apply (subgoal_tac "neg (number_of (Int.pred v)) = (number_of v < Suc 0) ")
apply (simp only: less_Suc_eq_le le_0_eq)
apply (subst less_number_of_Suc, simp)
done

text{*No longer required as a simprule because of the @{text inverse_fold}
   simproc*}
lemma Suc_diff_number_of:
     "Int.Pls < v ==>
      Suc m - (number_of v) = m - (number_of (Int.pred v))"
apply (subst Suc_diff_eq_diff_pred)
apply simp
apply (simp del: nat_numeral_1_eq_1)
apply (auto simp only: diff_nat_number_of less_0_number_of [symmetric]
                        neg_number_of_pred_iff_0)
done

lemma diff_Suc_eq_diff_pred: "m - Suc n = (m - 1) - n"
by (simp add: numerals split add: nat_diff_split)


subsubsection{*For @{term nat_case} and @{term nat_rec}*}

lemma nat_case_number_of [simp]:
     "nat_case a f (number_of v) =
        (let pv = number_of (Int.pred v) in
         if neg pv then a else f (nat pv))"
by (simp split add: nat.split add: Let_def neg_number_of_pred_iff_0)

lemma nat_case_add_eq_if [simp]:
     "nat_case a f ((number_of v) + n) =
       (let pv = number_of (Int.pred v) in
         if neg pv then nat_case a f n else f (nat pv + n))"
apply (subst add_eq_if)
apply (simp split add: nat.split
            del: nat_numeral_1_eq_1
            add: nat_numeral_1_eq_1 [symmetric]
                 numeral_1_eq_Suc_0 [symmetric]
                 neg_number_of_pred_iff_0)
done

lemma nat_rec_number_of [simp]:
     "nat_rec a f (number_of v) =
        (let pv = number_of (Int.pred v) in
         if neg pv then a else f (nat pv) (nat_rec a f (nat pv)))"
apply (case_tac " (number_of v) ::nat")
apply (simp_all (no_asm_simp) add: Let_def neg_number_of_pred_iff_0)
apply (simp split add: split_if_asm)
done

lemma nat_rec_add_eq_if [simp]:
     "nat_rec a f (number_of v + n) =
        (let pv = number_of (Int.pred v) in
         if neg pv then nat_rec a f n
                   else f (nat pv + n) (nat_rec a f (nat pv + n)))"
apply (subst add_eq_if)
apply (simp split add: nat.split
            del: nat_numeral_1_eq_1
            add: nat_numeral_1_eq_1 [symmetric]
                 numeral_1_eq_Suc_0 [symmetric]
                 neg_number_of_pred_iff_0)
done


subsubsection{*Various Other Lemmas*}

text {*Evens and Odds, for Mutilated Chess Board*}

text{*Lemmas for specialist use, NOT as default simprules*}
lemma nat_mult_2: "2 * z = (z+z::nat)"
proof -
  have "2*z = (1 + 1)*z" by simp
  also have "... = z+z" by (simp add: left_distrib)
  finally show ?thesis .
qed

lemma nat_mult_2_right: "z * 2 = (z+z::nat)"
by (subst mult_commute, rule nat_mult_2)

text{*Case analysis on @{term "n<2"}*}
lemma less_2_cases: "(n::nat) < 2 ==> n = 0 | n = Suc 0"
by arith

lemma div2_Suc_Suc [simp]: "Suc(Suc m) div 2 = Suc (m div 2)"
by arith

lemma add_self_div_2 [simp]: "(m + m) div 2 = (m::nat)"
by (simp add: nat_mult_2 [symmetric])

lemma mod2_Suc_Suc [simp]: "Suc(Suc(m)) mod 2 = m mod 2"
apply (subgoal_tac "m mod 2 < 2")
apply (erule less_2_cases [THEN disjE])
apply (simp_all (no_asm_simp) add: Let_def mod_Suc nat_1)
done

lemma mod2_gr_0 [simp]: "!!m::nat. (0 < m mod 2) = (m mod 2 = 1)"
apply (subgoal_tac "m mod 2 < 2")
apply (force simp del: mod_less_divisor, simp)
done

text{*Removal of Small Numerals: 0, 1 and (in additive positions) 2*}

lemma add_2_eq_Suc [simp]: "2 + n = Suc (Suc n)"
by simp

lemma add_2_eq_Suc' [simp]: "n + 2 = Suc (Suc n)"
by simp

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

lemmas Suc_div_eq_add3_div_number_of =
    Suc_div_eq_add3_div [of _ "number_of v", standard]
declare Suc_div_eq_add3_div_number_of [simp]

lemmas Suc_mod_eq_add3_mod_number_of =
    Suc_mod_eq_add3_mod [of _ "number_of v", standard]
declare Suc_mod_eq_add3_mod_number_of [simp]


subsubsection{*Special Simplification for Constants*}

text{*These belong here, late in the development of HOL, to prevent their
interfering with proofs of abstract properties of instances of the function
@{term number_of}*}

text{*These distributive laws move literals inside sums and differences.*}
lemmas left_distrib_number_of = left_distrib [of _ _ "number_of v", standard]
declare left_distrib_number_of [simp]

lemmas right_distrib_number_of = right_distrib [of "number_of v", standard]
declare right_distrib_number_of [simp]


lemmas left_diff_distrib_number_of =
    left_diff_distrib [of _ _ "number_of v", standard]
declare left_diff_distrib_number_of [simp]

lemmas right_diff_distrib_number_of =
    right_diff_distrib [of "number_of v", standard]
declare right_diff_distrib_number_of [simp]


text{*These are actually for fields, like real: but where else to put them?*}
lemmas zero_less_divide_iff_number_of =
    zero_less_divide_iff [of "number_of w", standard]
declare zero_less_divide_iff_number_of [simp,noatp]

lemmas divide_less_0_iff_number_of =
    divide_less_0_iff [of "number_of w", standard]
declare divide_less_0_iff_number_of [simp,noatp]

lemmas zero_le_divide_iff_number_of =
    zero_le_divide_iff [of "number_of w", standard]
declare zero_le_divide_iff_number_of [simp,noatp]

lemmas divide_le_0_iff_number_of =
    divide_le_0_iff [of "number_of w", standard]
declare divide_le_0_iff_number_of [simp,noatp]


(****
IF times_divide_eq_right and times_divide_eq_left are removed as simprules,
then these special-case declarations may be useful.

text{*These simprules move numerals into numerators and denominators.*}
lemma times_recip_eq_right [simp]: "a * (1/c) = a / (c::'a::field)"
by (simp add: times_divide_eq)

lemma times_recip_eq_left [simp]: "(1/c) * a = a / (c::'a::field)"
by (simp add: times_divide_eq)

lemmas times_divide_eq_right_number_of =
    times_divide_eq_right [of "number_of w", standard]
declare times_divide_eq_right_number_of [simp]

lemmas times_divide_eq_right_number_of =
    times_divide_eq_right [of _ _ "number_of w", standard]
declare times_divide_eq_right_number_of [simp]

lemmas times_divide_eq_left_number_of =
    times_divide_eq_left [of _ "number_of w", standard]
declare times_divide_eq_left_number_of [simp]

lemmas times_divide_eq_left_number_of =
    times_divide_eq_left [of _ _ "number_of w", standard]
declare times_divide_eq_left_number_of [simp]

****)

text {*Replaces @{text "inverse #nn"} by @{text "1/#nn"}.  It looks
  strange, but then other simprocs simplify the quotient.*}

lemmas inverse_eq_divide_number_of =
    inverse_eq_divide [of "number_of w", standard]
declare inverse_eq_divide_number_of [simp]


text {*These laws simplify inequalities, moving unary minus from a term
into the literal.*}
lemmas less_minus_iff_number_of =
    less_minus_iff [of "number_of v", standard]
declare less_minus_iff_number_of [simp,noatp]

lemmas le_minus_iff_number_of =
    le_minus_iff [of "number_of v", standard]
declare le_minus_iff_number_of [simp,noatp]

lemmas equation_minus_iff_number_of =
    equation_minus_iff [of "number_of v", standard]
declare equation_minus_iff_number_of [simp,noatp]


lemmas minus_less_iff_number_of =
    minus_less_iff [of _ "number_of v", standard]
declare minus_less_iff_number_of [simp,noatp]

lemmas minus_le_iff_number_of =
    minus_le_iff [of _ "number_of v", standard]
declare minus_le_iff_number_of [simp,noatp]

lemmas minus_equation_iff_number_of =
    minus_equation_iff [of _ "number_of v", standard]
declare minus_equation_iff_number_of [simp,noatp]


text{*To Simplify Inequalities Where One Side is the Constant 1*}

lemma less_minus_iff_1 [simp,noatp]:
  fixes b::"'b::{ordered_idom,number_ring}"
  shows "(1 < - b) = (b < -1)"
by auto

lemma le_minus_iff_1 [simp,noatp]:
  fixes b::"'b::{ordered_idom,number_ring}"
  shows "(1 \<le> - b) = (b \<le> -1)"
by auto

lemma equation_minus_iff_1 [simp,noatp]:
  fixes b::"'b::number_ring"
  shows "(1 = - b) = (b = -1)"
by (subst equation_minus_iff, auto)

lemma minus_less_iff_1 [simp,noatp]:
  fixes a::"'b::{ordered_idom,number_ring}"
  shows "(- a < 1) = (-1 < a)"
by auto

lemma minus_le_iff_1 [simp,noatp]:
  fixes a::"'b::{ordered_idom,number_ring}"
  shows "(- a \<le> 1) = (-1 \<le> a)"
by auto

lemma minus_equation_iff_1 [simp,noatp]:
  fixes a::"'b::number_ring"
  shows "(- a = 1) = (a = -1)"
by (subst minus_equation_iff, auto)


text {*Cancellation of constant factors in comparisons (@{text "<"} and @{text "\<le>"}) *}

lemmas mult_less_cancel_left_number_of =
    mult_less_cancel_left [of "number_of v", standard]
declare mult_less_cancel_left_number_of [simp,noatp]

lemmas mult_less_cancel_right_number_of =
    mult_less_cancel_right [of _ "number_of v", standard]
declare mult_less_cancel_right_number_of [simp,noatp]

lemmas mult_le_cancel_left_number_of =
    mult_le_cancel_left [of "number_of v", standard]
declare mult_le_cancel_left_number_of [simp,noatp]

lemmas mult_le_cancel_right_number_of =
    mult_le_cancel_right [of _ "number_of v", standard]
declare mult_le_cancel_right_number_of [simp,noatp]


text {*Multiplying out constant divisors in comparisons (@{text "<"}, @{text "\<le>"} and @{text "="}) *}

lemmas le_divide_eq_number_of1 [simp] = le_divide_eq [of _ _ "number_of w", standard]
lemmas divide_le_eq_number_of1 [simp] = divide_le_eq [of _ "number_of w", standard]
lemmas less_divide_eq_number_of1 [simp] = less_divide_eq [of _ _ "number_of w", standard]
lemmas divide_less_eq_number_of1 [simp] = divide_less_eq [of _ "number_of w", standard]
lemmas eq_divide_eq_number_of1 [simp] = eq_divide_eq [of _ _ "number_of w", standard]
lemmas divide_eq_eq_number_of1 [simp] = divide_eq_eq [of _ "number_of w", standard]


subsubsection{*Optional Simplification Rules Involving Constants*}

text{*Simplify quotients that are compared with a literal constant.*}

lemmas le_divide_eq_number_of = le_divide_eq [of "number_of w", standard]
lemmas divide_le_eq_number_of = divide_le_eq [of _ _ "number_of w", standard]
lemmas less_divide_eq_number_of = less_divide_eq [of "number_of w", standard]
lemmas divide_less_eq_number_of = divide_less_eq [of _ _ "number_of w", standard]
lemmas eq_divide_eq_number_of = eq_divide_eq [of "number_of w", standard]
lemmas divide_eq_eq_number_of = divide_eq_eq [of _ _ "number_of w", standard]


text{*Not good as automatic simprules because they cause case splits.*}
lemmas divide_const_simps =
  le_divide_eq_number_of divide_le_eq_number_of less_divide_eq_number_of
  divide_less_eq_number_of eq_divide_eq_number_of divide_eq_eq_number_of
  le_divide_eq_1 divide_le_eq_1 less_divide_eq_1 divide_less_eq_1

text{*Division By @{text "-1"}*}

lemma divide_minus1 [simp]:
     "x/-1 = -(x::'a::{field,division_by_zero,number_ring})"
by simp

lemma minus1_divide [simp]:
     "-1 / (x::'a::{field,division_by_zero,number_ring}) = - (1/x)"
by (simp add: divide_inverse inverse_minus_eq)

lemma half_gt_zero_iff:
     "(0 < r/2) = (0 < (r::'a::{ordered_field,division_by_zero,number_ring}))"
by auto

lemmas half_gt_zero = half_gt_zero_iff [THEN iffD2, standard]
declare half_gt_zero [simp]

(* The following lemma should appear in Divides.thy, but there the proof
   doesn't work. *)

lemma nat_dvd_not_less:
  "[| 0 < m; m < n |] ==> \<not> n dvd (m::nat)"
  by (unfold dvd_def) auto

ML {*
val divide_minus1 = @{thm divide_minus1};
val minus1_divide = @{thm minus1_divide};
*}

end
