(*  Title:      HOL/ex/BinEx.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header {* Binary arithmetic examples *}

theory BinEx = Main:

subsection {* The Integers *}

text {* Addition *}

lemma "(13::int) + 19 = 32"
  by simp

lemma "(1234::int) + 5678 = 6912"
  by simp

lemma "(1359::int) + -2468 = -1109"
  by simp

lemma "(93746::int) + -46375 = 47371"
  by simp


text {* \medskip Negation *}

lemma "- (65745::int) = -65745"
  by simp

lemma "- (-54321::int) = 54321"
  by simp


text {* \medskip Multiplication *}

lemma "(13::int) * 19 = 247"
  by simp

lemma "(-84::int) * 51 = -4284"
  by simp

lemma "(255::int) * 255 = 65025"
  by simp

lemma "(1359::int) * -2468 = -3354012"
  by simp

lemma "(89::int) * 10 \<noteq> 889"
  by simp

lemma "(13::int) < 18 - 4"
  by simp

lemma "(-345::int) < -242 + -100"
  by simp

lemma "(13557456::int) < 18678654"
  by simp

lemma "(999999::int) \<le> (1000001 + 1) - 2"
  by simp

lemma "(1234567::int) \<le> 1234567"
  by simp


text {* \medskip Quotient and Remainder *}

lemma "(10::int) div 3 = 3"
  by simp

lemma "(10::int) mod 3 = 1"
  by simp

text {* A negative divisor *}

lemma "(10::int) div -3 = -4"
  by simp

lemma "(10::int) mod -3 = -2"
  by simp

text {*
  A negative dividend\footnote{The definition agrees with mathematical
  convention but not with the hardware of most computers}
*}

lemma "(-10::int) div 3 = -4"
  by simp

lemma "(-10::int) mod 3 = 2"
  by simp

text {* A negative dividend \emph{and} divisor *}

lemma "(-10::int) div -3 = 3"
  by simp

lemma "(-10::int) mod -3 = -1"
  by simp

text {* A few bigger examples *}

lemma "(8452::int) mod 3 = 1"
  by simp

lemma "(59485::int) div 434 = 137"
  by simp

lemma "(1000006::int) mod 10 = 6"
  by simp


text {* \medskip Division by shifting *}

lemma "10000000 div 2 = (5000000::int)"
  by simp

lemma "10000001 mod 2 = (1::int)"
  by simp

lemma "10000055 div 32 = (312501::int)"
  by simp

lemma "10000055 mod 32 = (23::int)"
  by simp

lemma "100094 div 144 = (695::int)"
  by simp

lemma "100094 mod 144 = (14::int)"
  by simp


text {* \medskip Powers *}

lemma "2 ^ 10 = (1024::int)"
  by simp

lemma "-3 ^ 7 = (-2187::int)"
  by simp

lemma "13 ^ 7 = (62748517::int)"
  by simp

lemma "3 ^ 15 = (14348907::int)"
  by simp

lemma "-5 ^ 11 = (-48828125::int)"
  by simp


subsection {* The Natural Numbers *}

text {* Successor *}

lemma "Suc 99999 = 100000"
  by (simp add: Suc_nat_number_of)
    -- {* not a default rewrite since sometimes we want to have @{text "Suc #nnn"} *}


text {* \medskip Addition *}

lemma "(13::nat) + 19 = 32"
  by simp

lemma "(1234::nat) + 5678 = 6912"
  by simp

lemma "(973646::nat) + 6475 = 980121"
  by simp


text {* \medskip Subtraction *}

lemma "(32::nat) - 14 = 18"
  by simp

lemma "(14::nat) - 15 = 0"
  by simp

lemma "(14::nat) - 1576644 = 0"
  by simp

lemma "(48273776::nat) - 3873737 = 44400039"
  by simp


text {* \medskip Multiplication *}

lemma "(12::nat) * 11 = 132"
  by simp

lemma "(647::nat) * 3643 = 2357021"
  by simp


text {* \medskip Quotient and Remainder *}

lemma "(10::nat) div 3 = 3"
  by simp

lemma "(10::nat) mod 3 = 1"
  by simp

lemma "(10000::nat) div 9 = 1111"
  by simp

lemma "(10000::nat) mod 9 = 1"
  by simp

lemma "(10000::nat) div 16 = 625"
  by simp

lemma "(10000::nat) mod 16 = 0"
  by simp


text {* \medskip Powers *}

lemma "2 ^ 12 = (4096::nat)"
  by simp

lemma "3 ^ 10 = (59049::nat)"
  by simp

lemma "12 ^ 7 = (35831808::nat)"
  by simp

lemma "3 ^ 14 = (4782969::nat)"
  by simp

lemma "5 ^ 11 = (48828125::nat)"
  by simp


text {* \medskip Testing the cancellation of complementary terms *}

lemma "y + (x + -x) = (0::int) + y"
  by simp

lemma "y + (-x + (- y + x)) = (0::int)"
  by simp

lemma "-x + (y + (- y + x)) = (0::int)"
  by simp

lemma "x + (x + (- x + (- x + (- y + - z)))) = (0::int) - y - z"
  by simp

lemma "x + x - x - x - y - z = (0::int) - y - z"
  by simp

lemma "x + y + z - (x + z) = y - (0::int)"
  by simp

lemma "x + (y + (y + (y + (-x + -x)))) = (0::int) + y - x + y + y"
  by simp

lemma "x + (y + (y + (y + (-y + -x)))) = y + (0::int) + y"
  by simp

lemma "x + y - x + z - x - y - z + x < (1::int)"
  by simp


subsection {* Normal form of bit strings *}

text {*
  Definition of normal form for proving that binary arithmetic on
  normalized operands yields normalized results.  Normal means no
  leading 0s on positive numbers and no leading 1s on negatives.
*}

consts normal :: "bin set"
inductive normal
  intros
    Pls [simp]: "Pls: normal"
    Min [simp]: "Min: normal"
    BIT_F [simp]: "w: normal ==> w \<noteq> Pls ==> w BIT False : normal"
    BIT_T [simp]: "w: normal ==> w \<noteq> Min ==> w BIT True : normal"

text {*
  \medskip Binary arithmetic on normalized operands yields normalized
  results.
*}

lemma normal_BIT_I [simp]: "w BIT b \<in> normal ==> w BIT b BIT c \<in> normal"
  apply (case_tac c)
   apply auto
  done

lemma normal_BIT_D: "w BIT b \<in> normal ==> w \<in> normal"
  apply (erule normal.cases)
     apply auto
  done

lemma NCons_normal [simp]: "w \<in> normal ==> NCons w b \<in> normal"
  apply (induct w)
    apply (auto simp add: NCons_Pls NCons_Min)
  done

lemma NCons_True: "NCons w True \<noteq> Pls"
  apply (induct w)
    apply auto
  done

lemma NCons_False: "NCons w False \<noteq> Min"
  apply (induct w)
    apply auto
  done

lemma bin_succ_normal [simp]: "w \<in> normal ==> bin_succ w \<in> normal"
  apply (erule normal.induct)
     apply (case_tac [4] w)
  apply (auto simp add: NCons_True bin_succ_BIT)
  done

lemma bin_pred_normal [simp]: "w \<in> normal ==> bin_pred w \<in> normal"
  apply (erule normal.induct)
     apply (case_tac [3] w)
  apply (auto simp add: NCons_False bin_pred_BIT)
  done

lemma bin_add_normal [rule_format]:
  "w \<in> normal --> (\<forall>z. z \<in> normal --> bin_add w z \<in> normal)"
  apply (induct w)
    apply simp
   apply simp
  apply (rule impI)
  apply (rule allI)
  apply (induct_tac z)
    apply (simp_all add: bin_add_BIT)
  apply (safe dest!: normal_BIT_D)
    apply simp_all
  done

lemma normal_Pls_eq_0: "w \<in> normal ==> (w = Pls) = (number_of w = (0::int))"
  apply (erule normal.induct)
     apply auto
  done
(*
lemma bin_minus_normal: "w \<in> normal ==> bin_minus w \<in> normal"
  apply (erule normal.induct)
     apply (simp_all add: bin_minus_BIT)
  apply (rule normal.intros)
   apply assumption
  apply (simp add: normal_Pls_eq_0)
  apply (simp only: number_of_minus iszero_def zminus_equation [of _ "0"])

The previous command should have finished the proof but the lin-arith
procedure at the end of simplificatioon fails.
Problem: lin-arith correctly derives the contradictory thm
"number_of w + 1 + - 0 \<le> 0 + number_of w"  [..]
which its local simplification setup should turn into False.
But on the way we get

Procedure "int_add_eval_numerals" produced rewrite rule:
number_of ?v3 + 1 \<equiv> number_of (bin_add ?v3 (Pls BIT True))

and eventually we arrive not at false but at

"\<not> neg (number_of (bin_add w (bin_minus (bin_add w (Pls BIT True)))))"

The next 2 commands should now be obsolete:
  apply (rule not_sym)
  apply simp
  done

needs the previous thm:
lemma bin_mult_normal [rule_format]:
    "w \<in> normal ==> z \<in> normal --> bin_mult w z \<in> normal"
  apply (erule normal.induct)
     apply (simp_all add: bin_minus_normal bin_mult_BIT)
  apply (safe dest!: normal_BIT_D)
  apply (simp add: bin_add_normal)
  done
*)
end
