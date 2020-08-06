(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for conversions for algebraically founded bit word types\<close>

theory Word_Conversions
  imports
    Main
    "HOL-Library.Type_Length"
    "HOL-Library.Bit_Operations"
    "HOL-Word.Word"
begin

context semiring_1
begin

lift_definition unsigned :: \<open>'b::len word \<Rightarrow> 'a\<close>
  is \<open>of_nat \<circ> nat \<circ> take_bit LENGTH('b)\<close>
  by simp

lemma unsigned_0 [simp]:
  \<open>unsigned 0 = 0\<close>
  by transfer simp

lemma unsigned_1 [simp]:
  \<open>unsigned 1 = 1\<close>
  by transfer simp

end

lemma unat_unsigned:
  \<open>unat = unsigned\<close>
  by transfer simp

lemma uint_unsigned:
  \<open>uint = unsigned\<close>
  by transfer (simp add: fun_eq_iff)

context semiring_char_0
begin

lemma unsigned_word_eqI:
  \<open>v = w\<close> if \<open>unsigned v = unsigned w\<close>
  using that by transfer (simp add: eq_nat_nat_iff)

lemma word_eq_iff_unsigned:
  \<open>v = w \<longleftrightarrow> unsigned v = unsigned w\<close>
  by (auto intro: unsigned_word_eqI)

end

context ring_1
begin

lift_definition signed :: \<open>'b::len word \<Rightarrow> 'a\<close>
  is \<open>of_int \<circ> signed_take_bit (LENGTH('b) - 1)\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma signed_0 [simp]:
  \<open>signed 0 = 0\<close>
  by transfer simp

lemma signed_1 [simp]:
  \<open>signed (1 :: 'b::len word) = (if LENGTH('b) = 1 then - 1 else 1)\<close>
  by (transfer fixing: uminus)
    (simp_all add: signed_take_bit_eq not_le Suc_lessI)

lemma signed_minus_1 [simp]:
  \<open>signed (- 1 :: 'b::len word) = - 1\<close>
  by (transfer fixing: uminus) simp

end

lemma sint_signed:
  \<open>sint = signed\<close>
  by transfer simp

context ring_char_0
begin

lemma signed_word_eqI:
  \<open>v = w\<close> if \<open>signed v = signed w\<close>
  using that by transfer (simp flip: signed_take_bit_decr_length_iff)

lemma word_eq_iff_signed:
  \<open>v = w \<longleftrightarrow> signed v = signed w\<close>
  by (auto intro: signed_word_eqI)

end

abbreviation nat_of_word :: \<open>'a::len word \<Rightarrow> nat\<close>
  where \<open>nat_of_word \<equiv> unsigned\<close>

abbreviation unsigned_int :: \<open>'a::len word \<Rightarrow> int\<close>
  where \<open>unsigned_int \<equiv> unsigned\<close>

abbreviation signed_int :: \<open>'a::len word \<Rightarrow> int\<close>
  where \<open>signed_int \<equiv> signed\<close>

abbreviation word_of_nat :: \<open>nat \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_nat \<equiv> of_nat\<close>

abbreviation word_of_int :: \<open>int \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_int \<equiv> of_int\<close>

text \<open>TODO rework names from here\<close>

lemma unsigned_of_nat [simp]:
  \<open>unsigned (of_nat n :: 'a::len word) = take_bit LENGTH('a) n\<close>
  by transfer (simp add: nat_eq_iff take_bit_of_nat)

lemma of_nat_unsigned [simp]:
  \<open>of_nat (unsigned w) = w\<close>
  by transfer simp

lemma of_int_unsigned [simp]:
  \<open>of_int (unsigned w) = w\<close>
  by transfer simp

lemma unsigned_int_greater_eq:
  \<open>(0::int) \<le> unsigned w\<close> for w :: \<open>'a::len word\<close>
  by transfer simp

lemma unsigned_nat_less:
  \<open>unsigned w < (2 ^ LENGTH('a) :: nat)\<close> for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_eq_mod)

lemma unsigned_int_less:
  \<open>unsigned w < (2 ^ LENGTH('a) :: int)\<close> for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_eq_mod)

lemma signed_of_int [simp]:
  \<open>signed (of_int k :: 'a::len word) = signed_take_bit (LENGTH('a) - 1) k\<close>
  by transfer simp

lemma of_int_signed [simp]:
  \<open>of_int (signed a) = a\<close>
  by transfer (simp_all add: take_bit_signed_take_bit)

lemma signed_int_greater_eq:
  \<open>- ((2::int) ^ (LENGTH('a) - 1)) \<le> signed w\<close> for w :: \<open>'a::len word\<close>
proof (cases \<open>bit w (LENGTH('a) - 1)\<close>)
  case True
  then show ?thesis
    by transfer (simp add: signed_take_bit_eq_or minus_exp_eq_not_mask or_greater_eq ac_simps)
next
  have *: \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> (0::int)\<close>
    by simp
  case False
  then show ?thesis
    by transfer (auto simp add: signed_take_bit_eq intro: order_trans *)
qed

lemma signed_int_less:
  \<open>signed w < (2 ^ (LENGTH('a) - 1) :: int)\<close> for w :: \<open>'a::len word\<close>
  by (cases \<open>bit w (LENGTH('a) - 1)\<close>; transfer)
    (simp_all add: signed_take_bit_eq signed_take_bit_eq_or take_bit_int_less_exp not_eq_complement mask_eq_exp_minus_1 OR_upper)

context linordered_semidom
begin

lemma word_less_eq_iff_unsigned:
  "a \<le> b \<longleftrightarrow> unsigned a \<le> unsigned b"
  by (transfer fixing: less_eq) (simp add: nat_le_eq_zle)

lemma word_less_iff_unsigned:
  "a < b \<longleftrightarrow> unsigned a < unsigned b"
  by (transfer fixing: less) (auto dest: preorder_class.le_less_trans [OF take_bit_nonnegative])

end

lemma of_nat_word_eq_iff:
  \<open>of_nat m = (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m = take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_less_eq_iff:
  \<open>of_nat m \<le> (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m \<le> take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_less_iff:
  \<open>of_nat m < (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m < take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_eq_0_iff:
  \<open>of_nat n = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd n\<close>
  using of_nat_word_eq_iff [where ?'a = 'a, of n 0] by (simp add: take_bit_eq_0_iff)

lemma of_int_word_eq_iff:
  \<open>of_int k = (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_less_eq_iff:
  \<open>of_int k \<le> (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k \<le> take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_less_iff:
  \<open>of_int k < (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k < take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_eq_0_iff:
  \<open>of_int k = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd k\<close>
  using of_int_word_eq_iff [where ?'a = 'a, of k 0] by (simp add: take_bit_eq_0_iff)

end
