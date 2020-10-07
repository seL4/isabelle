(*  Author:     Jeremy Dawson, NICTA
*)

section \<open>Operation variant for the most significant bit\<close>

theory Misc_msb
  imports
    Word
    Reversed_Bit_Lists
begin

class msb =
  fixes msb :: \<open>'a \<Rightarrow> bool\<close>

instantiation int :: msb
begin

definition \<open>msb x \<longleftrightarrow> x < 0\<close> for x :: int

instance ..

end

lemma msb_conv_bin_sign: "msb x \<longleftrightarrow> bin_sign x = -1"
by(simp add: bin_sign_def not_le msb_int_def)

lemma msb_bin_rest [simp]: "msb (bin_rest x) = msb x"
by(simp add: msb_int_def)

lemma int_msb_and [simp]: "msb ((x :: int) AND y) \<longleftrightarrow> msb x \<and> msb y"
by(simp add: msb_int_def)

lemma int_msb_or [simp]: "msb ((x :: int) OR y) \<longleftrightarrow> msb x \<or> msb y"
by(simp add: msb_int_def)

lemma int_msb_xor [simp]: "msb ((x :: int) XOR y) \<longleftrightarrow> msb x \<noteq> msb y"
by(simp add: msb_int_def)

lemma int_msb_not [simp]: "msb (NOT (x :: int)) \<longleftrightarrow> \<not> msb x"
by(simp add: msb_int_def not_less)

lemma msb_shiftl [simp]: "msb ((x :: int) << n) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_shiftr [simp]: "msb ((x :: int) >> r) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_bin_sc [simp]: "msb (bin_sc n b x) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign)

lemma msb_0 [simp]: "msb (0 :: int) = False"
by(simp add: msb_int_def)

lemma msb_1 [simp]: "msb (1 :: int) = False"
by(simp add: msb_int_def)

lemma msb_numeral [simp]:
  "msb (numeral n :: int) = False"
  "msb (- numeral n :: int) = True"
by(simp_all add: msb_int_def)

instantiation word :: (len) msb
begin

definition msb_word :: \<open>'a word \<Rightarrow> bool\<close>
  where \<open>msb a \<longleftrightarrow> bin_sign (sbintrunc (LENGTH('a) - 1) (uint a)) = - 1\<close>

lemma msb_word_eq:
  \<open>msb w \<longleftrightarrow> bit w (LENGTH('a) - 1)\<close> for w :: \<open>'a::len word\<close>
  by (simp add: msb_word_def bin_sign_lem bit_uint_iff)

instance ..

end

lemma msb_word_iff_bit:
  \<open>msb w \<longleftrightarrow> bit w (LENGTH('a) - Suc 0)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: msb_word_def bin_sign_def bit_uint_iff)

lemma word_msb_def:
  "msb a \<longleftrightarrow> bin_sign (sint a) = - 1"
  by (simp add: msb_word_def sint_uint)

lemma word_msb_sint: "msb w \<longleftrightarrow> sint w < 0"
  by (simp add: msb_word_eq bit_last_iff)

lemma msb_word_iff_sless_0:
  \<open>msb w \<longleftrightarrow> w <s 0\<close>
  by (simp add: word_msb_sint word_sless_alt)

lemma msb_word_of_int: "msb (word_of_int x::'a::len word) = bin_nth x (LENGTH('a) - 1)"
  by (simp add: word_msb_def word_sbin.eq_norm bin_sign_lem)

lemma word_msb_numeral [simp]:
  "msb (numeral w::'a::len word) = bin_nth (numeral w) (LENGTH('a) - 1)"
  unfolding word_numeral_alt by (rule msb_word_of_int)

lemma word_msb_neg_numeral [simp]:
  "msb (- numeral w::'a::len word) = bin_nth (- numeral w) (LENGTH('a) - 1)"
  unfolding word_neg_numeral_alt by (rule msb_word_of_int)

lemma word_msb_0 [simp]: "\<not> msb (0::'a::len word)"
  by (simp add: word_msb_def bin_sign_def sint_uint sbintrunc_eq_take_bit)

lemma word_msb_1 [simp]: "msb (1::'a::len word) \<longleftrightarrow> LENGTH('a) = 1"
  unfolding word_1_wi msb_word_of_int eq_iff [where 'a=nat]
  by (simp add: Suc_le_eq)

lemma word_msb_nth: "msb w = bin_nth (uint w) (LENGTH('a) - 1)"
  for w :: "'a::len word"
  by (simp add: word_msb_def sint_uint bin_sign_lem)

lemma word_msb_alt: "msb w \<longleftrightarrow> hd (to_bl w)"
  for w :: "'a::len word"
  apply (simp add: msb_word_eq)
  apply (subst hd_conv_nth)
   apply simp
  apply (subst nth_to_bl)
   apply simp
  apply simp
  done

lemma msb_nth: "msb w = w !! (LENGTH('a) - 1)"
  for w :: "'a::len word"
  by (simp add: word_msb_nth word_test_bit_def)

lemma word_msb_n1 [simp]: "msb (-1::'a::len word)"
  by (simp add: msb_word_eq exp_eq_zero_iff not_le)

lemma msb_shift: "msb w \<longleftrightarrow> w >> (LENGTH('a) - 1) \<noteq> 0"
  for w :: "'a::len word"
  by (simp add: msb_word_eq shiftr_word_eq bit_iff_odd_drop_bit drop_bit_eq_zero_iff_not_bit_last)

lemmas word_ops_msb = msb1 [unfolded msb_nth [symmetric, unfolded One_nat_def]]

end
