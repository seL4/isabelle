(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for conversions for algebraically founded bit word types\<close>

theory Conversions
  imports
    Main
    "HOL-Library.Type_Length"
    "HOL-Library.Bit_Operations"
    "HOL-Word.Word"
begin

hide_const (open) unat uint sint word_of_int ucast scast

subsection \<open>Conversions to words\<close>

abbreviation word_of_nat :: \<open>nat \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_nat \<equiv> of_nat\<close>

abbreviation word_of_int :: \<open>int \<Rightarrow> 'a::len word\<close>
  where \<open>word_of_int \<equiv> of_int\<close>

lemma Word_eq_word_of_int [simp]:
  \<open>Word.Word = word_of_int\<close>
  by (rule ext; transfer) simp

lemma word_of_nat_eq_iff:
  \<open>word_of_nat m = (word_of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m = take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma word_of_int_eq_iff:
  \<open>word_of_int k = (word_of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by transfer rule

lemma word_of_nat_less_eq_iff:
  \<open>word_of_nat m \<le> (word_of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m \<le> take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma word_of_int_less_eq_iff:
  \<open>word_of_int k \<le> (word_of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k \<le> take_bit LENGTH('a) l\<close>
  by transfer rule

lemma word_of_nat_less_iff:
  \<open>word_of_nat m < (word_of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m < take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma word_of_int_less_iff:
  \<open>word_of_int k < (word_of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k < take_bit LENGTH('a) l\<close>
  by transfer rule

lemma word_of_nat_eq_0_iff [simp]:
  \<open>word_of_nat n = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd n\<close>
  using of_nat_word_eq_iff [where ?'a = 'a, of n 0] by (simp add: take_bit_eq_0_iff)

lemma word_of_int_eq_0_iff [simp]:
  \<open>word_of_int k = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd k\<close>
  using of_int_word_eq_iff [where ?'a = 'a, of k 0] by (simp add: take_bit_eq_0_iff)

lemma int_AND_eq:
  \<open>int (m AND n) = int m AND int n\<close>
  by (rule bit_eqI) (simp add: bit_and_iff)

lemma int_OR_eq:
  \<open>int (m OR n) = int m OR int n\<close>
  by (rule bit_eqI) (simp add: bit_or_iff)

lemma int_XOR_eq:
  \<open>int (m XOR n) = int m XOR int n\<close>
  by (rule bit_eqI) (simp add: bit_xor_iff)

context semiring_bit_operations
begin

lemma push_bit_and [simp]:
  \<open>push_bit n (a AND b) = push_bit n a AND push_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_push_bit_iff bit_and_iff)

lemma push_bit_or [simp]:
  \<open>push_bit n (a OR b) = push_bit n a OR push_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_push_bit_iff bit_or_iff)

lemma push_bit_xor [simp]:
  \<open>push_bit n (a XOR b) = push_bit n a XOR push_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_push_bit_iff bit_xor_iff)

lemma drop_bit_and [simp]:
  \<open>drop_bit n (a AND b) = drop_bit n a AND drop_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_drop_bit_eq bit_and_iff)

lemma drop_bit_or [simp]:
  \<open>drop_bit n (a OR b) = drop_bit n a OR drop_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_drop_bit_eq bit_or_iff)

lemma drop_bit_xor [simp]:
  \<open>drop_bit n (a XOR b) = drop_bit n a XOR drop_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_drop_bit_eq bit_xor_iff)

end

lemma bit_word_of_nat_iff:
  \<open>bit (word_of_nat m :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> bit m n\<close>
  by transfer simp

lemma bit_word_of_int_iff:
  \<open>bit (word_of_int k :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> bit k n\<close>
  by transfer simp

lemma word_of_nat_AND_eq:
  \<open>word_of_nat (m AND n) = word_of_nat m AND word_of_nat n\<close>
  by (rule bit_eqI) (auto simp add: bit_word_of_nat_iff bit_and_iff)

lemma word_of_int_AND_eq:
  \<open>word_of_int (k AND l) = word_of_int k AND word_of_int l\<close>
  by (rule bit_eqI) (auto simp add: bit_word_of_int_iff bit_and_iff)

lemma word_of_nat_OR_eq:
  \<open>word_of_nat (m OR n) = word_of_nat m OR word_of_nat n\<close>
  by (rule bit_eqI) (auto simp add: bit_word_of_nat_iff bit_or_iff)

lemma word_of_int_OR_eq:
  \<open>word_of_int (k OR l) = word_of_int k OR word_of_int l\<close>
  by (rule bit_eqI) (auto simp add: bit_word_of_int_iff bit_or_iff)

lemma word_of_nat_XOR_eq:
  \<open>word_of_nat (m XOR n) = word_of_nat m XOR word_of_nat n\<close>
  by (rule bit_eqI) (auto simp add: bit_word_of_nat_iff bit_xor_iff)

lemma word_of_int_XOR_eq:
  \<open>word_of_int (k XOR l) = word_of_int k XOR word_of_int l\<close>
  by (rule bit_eqI) (auto simp add: bit_word_of_int_iff bit_xor_iff)


subsection \<open>Conversion from words\<close>

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

context ring_char_0
begin

lemma signed_word_eqI:
  \<open>v = w\<close> if \<open>signed v = signed w\<close>
  using that by transfer (simp flip: signed_take_bit_decr_length_iff)

lemma word_eq_iff_signed:
  \<open>v = w \<longleftrightarrow> signed v = signed w\<close>
  by (auto intro: signed_word_eqI)

end

abbreviation unat :: \<open>'a::len word \<Rightarrow> nat\<close>
  where \<open>unat \<equiv> unsigned\<close>

abbreviation uint :: \<open>'a::len word \<Rightarrow> int\<close>
  where \<open>uint \<equiv> unsigned\<close>

abbreviation sint :: \<open>'a::len word \<Rightarrow> int\<close>
  where \<open>sint \<equiv> signed\<close>

abbreviation ucast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>ucast \<equiv> unsigned\<close>

abbreviation scast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>scast \<equiv> signed\<close>

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>(pcr_word ===> (=)) (nat \<circ> take_bit LENGTH('a)) (unat :: 'a::len word \<Rightarrow> nat)\<close>
  using unsigned.transfer [where ?'a = nat] by simp

lemma [transfer_rule]:
  \<open>(pcr_word ===> (=)) (take_bit LENGTH('a)) (uint :: 'a::len word \<Rightarrow> int)\<close>
  using unsigned.transfer [where ?'a = int] by (simp add: comp_def)

lemma [transfer_rule]:
  \<open>(pcr_word ===> (=)) (signed_take_bit (LENGTH('a) - Suc 0)) (sint :: 'a::len word \<Rightarrow> int)\<close>
  using signed.transfer [where ?'a = int] by simp

lemma [transfer_rule]:
  \<open>(pcr_word ===> pcr_word) (take_bit LENGTH('a)) (ucast :: 'a::len word \<Rightarrow> 'b::len word)\<close>
proof (rule rel_funI)
  fix k :: int and w :: \<open>'a word\<close>
  assume \<open>pcr_word k w\<close>
  then have \<open>w = word_of_int k\<close>
    by (simp add: pcr_word_def cr_word_def relcompp_apply)
  moreover have \<open>pcr_word (take_bit LENGTH('a) k) (ucast (word_of_int k :: 'a word))\<close>
    by transfer (simp add: pcr_word_def cr_word_def relcompp_apply)
  ultimately show \<open>pcr_word (take_bit LENGTH('a) k) (ucast w)\<close>
    by simp
qed

lemma [transfer_rule]:
  \<open>(pcr_word ===> pcr_word) (signed_take_bit (LENGTH('a) - 1)) (scast :: 'a::len word \<Rightarrow> 'b::len word)\<close>
proof (rule rel_funI)
  fix k :: int and w :: \<open>'a word\<close>
  assume \<open>pcr_word k w\<close>
  then have \<open>w = word_of_int k\<close>
    by (simp add: pcr_word_def cr_word_def relcompp_apply)
  moreover have \<open>pcr_word (signed_take_bit (LENGTH('a) - 1) k) (scast (word_of_int k :: 'a word))\<close>
    by transfer (simp add: pcr_word_def cr_word_def relcompp_apply)
  ultimately show \<open>pcr_word (signed_take_bit (LENGTH('a) - 1) k) (scast w)\<close>
    by simp
qed

end

lemma unsigned_of_nat [simp]:
  \<open>unsigned (of_nat n :: 'a::len word) = of_nat (take_bit LENGTH('a) n)\<close>
  by transfer (simp add: nat_eq_iff take_bit_of_nat)

lemma of_nat_unat [simp]:
  \<open>of_nat (unat w) = unsigned w\<close>
  by transfer simp

lemma of_int_uint [simp]:
  \<open>of_int (uint w) = unsigned w\<close>
  by transfer simp

context unique_euclidean_semiring_numeral
begin

lemma unsigned_greater_eq:
  \<open>0 \<le> unsigned w\<close> for w :: \<open>'b::len word\<close>
  by (transfer fixing: less_eq) simp

lemma unsigned_less:
  \<open>unsigned w < 2 ^ LENGTH('b)\<close> for w :: \<open>'b::len word\<close>
  by (transfer fixing: less) (simp add: take_bit_int_less_exp)

end

context linordered_semidom
begin

lemma word_less_eq_iff_unsigned:
  "a \<le> b \<longleftrightarrow> unsigned a \<le> unsigned b"
  by (transfer fixing: less_eq) (simp add: nat_le_eq_zle)

lemma word_less_iff_unsigned:
  "a < b \<longleftrightarrow> unsigned a < unsigned b"
  by (transfer fixing: less) (auto dest: preorder_class.le_less_trans [OF take_bit_nonnegative])

end

lemma signed_of_int [simp]:
  \<open>signed (word_of_int k :: 'a::len word) = of_int (signed_take_bit (LENGTH('a) - 1) k)\<close>
  by transfer simp

lemma of_int_sint [simp]:
  \<open>of_int (sint a) = signed a\<close>
  by transfer (simp_all add: take_bit_signed_take_bit)

lemma sint_greater_eq:
  \<open>- (2 ^ (LENGTH('a) - 1)) \<le> sint w\<close> for w :: \<open>'a::len word\<close>
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

lemma sint_less:
  \<open>sint w < 2 ^ (LENGTH('a) - 1)\<close> for w :: \<open>'a::len word\<close>
  by (cases \<open>bit w (LENGTH('a) - 1)\<close>; transfer)
    (simp_all add: signed_take_bit_eq signed_take_bit_eq_or take_bit_int_less_exp not_eq_complement mask_eq_exp_minus_1 OR_upper)

end
