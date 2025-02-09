(*  Title:      HOL/ex/Word_Msb.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>An attempt for msb on word\<close>


theory Word_Msb
  imports "HOL-Library.Word"
begin

class word = ring_bit_operations +
  fixes word_length :: \<open>'a itself \<Rightarrow> nat\<close>
  assumes word_length_positive [simp]: \<open>0 < word_length TYPE('a)\<close>
    and possible_bit_msb: \<open>possible_bit TYPE('a) (word_length TYPE('a) - Suc 0)\<close>
    and not_possible_bit_length: \<open>\<not> possible_bit TYPE('a) (word_length TYPE('a))\<close>
begin

lemma word_length_not_0 [simp]:
  \<open>word_length TYPE('a) \<noteq> 0\<close>
  using word_length_positive
  by simp

lemma possible_bit_iff_less_word_length:
  \<open>possible_bit TYPE('a) n \<longleftrightarrow> n < word_length TYPE('a)\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume \<open>?P\<close>
  show ?Q
  proof (rule ccontr)
    assume \<open>\<not> n < word_length TYPE('a)\<close>
    then have \<open>word_length TYPE('a) \<le> n\<close>
      by simp
    with \<open>?P\<close> have \<open>possible_bit TYPE('a) (word_length TYPE('a))\<close>
      by (rule possible_bit_less_imp)
    with not_possible_bit_length show False ..
  qed
next
  assume \<open>?Q\<close>
  then have \<open>n \<le> word_length TYPE('a) - Suc 0\<close>
    by simp
  with possible_bit_msb show ?P
    by (rule possible_bit_less_imp)
qed

end

instantiation word :: (len) word
begin

definition word_length_word :: \<open>'a word itself \<Rightarrow> nat\<close>
  where [simp, code_unfold]: \<open>word_length_word _ = LENGTH('a)\<close>

instance
  by standard simp_all

end

context word
begin

context
  includes bit_operations_syntax
begin

definition msb :: \<open>'a \<Rightarrow> bool\<close>
  where \<open>msb w = bit w (word_length TYPE('a) - Suc 0)\<close>

lemma not_msb_0 [simp]:
  \<open>\<not> msb 0\<close>
  by (simp add: msb_def)

lemma msb_minus_1 [simp]:
  \<open>msb (- 1)\<close>
  by (simp add: msb_def possible_bit_iff_less_word_length)

lemma msb_1_iff [simp]:
  \<open>msb 1 \<longleftrightarrow> word_length TYPE('a) = 1\<close>
  by (auto simp add: msb_def bit_simps le_less)

lemma msb_minus_iff [simp]:
  \<open>msb (- w) \<longleftrightarrow> \<not> msb (w - 1)\<close>
  by (simp add: msb_def bit_simps possible_bit_iff_less_word_length)

lemma msb_not_iff [simp]:
  \<open>msb (NOT w) \<longleftrightarrow> \<not> msb w\<close>
  by (simp add: msb_def bit_simps possible_bit_iff_less_word_length)

lemma msb_and_iff [simp]:
  \<open>msb (v AND w) \<longleftrightarrow> msb v \<and> msb w\<close>
  by (simp add: msb_def bit_simps)

lemma msb_or_iff [simp]:
  \<open>msb (v OR w) \<longleftrightarrow> msb v \<or> msb w\<close>
  by (simp add: msb_def bit_simps)

lemma msb_xor_iff [simp]:
  \<open>msb (v XOR w) \<longleftrightarrow> \<not> (msb v \<longleftrightarrow> msb w)\<close>
  by (simp add: msb_def bit_simps)

lemma msb_exp_iff [simp]:
  \<open>msb (2 ^ n) \<longleftrightarrow> n = word_length TYPE('a) - Suc 0\<close>
  by (auto simp add: msb_def bit_simps possible_bit_iff_less_word_length)

lemma msb_mask_iff [simp]:
  \<open>msb (mask n) \<longleftrightarrow> word_length TYPE('a) \<le> n\<close>
  by (simp add: msb_def bit_simps less_diff_conv2 Suc_le_eq less_Suc_eq_le possible_bit_iff_less_word_length)

lemma msb_set_bit_iff [simp]:
  \<open>msb (set_bit n w) \<longleftrightarrow> n = word_length TYPE('a) - Suc 0 \<or> msb w\<close>
  by (simp add: set_bit_eq_or ac_simps)

lemma msb_unset_bit_iff [simp]:
  \<open>msb (unset_bit n w) \<longleftrightarrow> n \<noteq> word_length TYPE('a) - Suc 0 \<and> msb w\<close>
  by (simp add: unset_bit_eq_and_not ac_simps)

lemma msb_flip_bit_iff [simp]:
  \<open>msb (flip_bit n w) \<longleftrightarrow> (n \<noteq> word_length TYPE('a) - Suc 0 \<longleftrightarrow> msb w)\<close>
  by (auto simp add: flip_bit_eq_xor)

lemma msb_push_bit_iff:
  \<open>msb (push_bit n w) \<longleftrightarrow> n < word_length TYPE('a) \<and> bit w (word_length TYPE('a) - Suc n)\<close>
  by (simp add: msb_def bit_simps le_diff_conv2 Suc_le_eq possible_bit_iff_less_word_length)

lemma msb_drop_bit_iff [simp]:
  \<open>msb (drop_bit n w) \<longleftrightarrow> n = 0 \<and> msb w\<close>
  by (cases n)
    (auto simp add: msb_def bit_simps possible_bit_iff_less_word_length intro!: impossible_bit)

lemma msb_take_bit_iff [simp]:
  \<open>msb (take_bit n w) \<longleftrightarrow> word_length TYPE('a) \<le> n \<and> msb w\<close>
  by (simp add: take_bit_eq_mask ac_simps)

lemma msb_signed_take_bit_iff:
  \<open>msb (signed_take_bit n w) \<longleftrightarrow> bit w (min n (word_length TYPE('a) - Suc 0))\<close>
  by (simp add: msb_def bit_simps possible_bit_iff_less_word_length)

definition signed_drop_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>signed_drop_bit n w = drop_bit n w
    OR (of_bool (bit w (word_length TYPE('a) - Suc 0)) * NOT (mask (word_length TYPE('a) - Suc n)))\<close>

lemma msb_signed_drop_bit_iff [simp]:
  \<open>msb (signed_drop_bit n w) \<longleftrightarrow> msb w\<close>
  by (simp add: signed_drop_bit_def bit_simps not_le not_less)
    (simp add: msb_def)

end

end

end
