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


subsection \<open>Conversions to word\<close>

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


subsection \<open>Conversion from word\<close>

subsubsection \<open>Generic unsigned conversion\<close>

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

context semiring_bits
begin

lemma bit_unsigned_iff:
  \<open>bit (unsigned w) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> bit w n\<close>
  for w :: \<open>'b::len word\<close>
  by (transfer fixing: bit) (simp add: bit_of_nat_iff bit_nat_iff bit_take_bit_iff)

end

context semiring_bit_shifts
begin

lemma unsigned_push_bit_eq:
  \<open>unsigned (push_bit n w) = take_bit LENGTH('b) (push_bit n (unsigned w))\<close>
  for w :: \<open>'b::len word\<close>
proof (rule bit_eqI)
  fix m
  assume \<open>2 ^ m \<noteq> 0\<close>
  show \<open>bit (unsigned (push_bit n w)) m = bit (take_bit LENGTH('b) (push_bit n (unsigned w))) m\<close>
  proof (cases \<open>n \<le> m\<close>)
    case True
    with \<open>2 ^ m \<noteq> 0\<close> have \<open>2 ^ (m - n) \<noteq> 0\<close>
      by (metis (full_types) diff_add exp_add_not_zero_imp)
    with True show ?thesis
      by (simp add: bit_unsigned_iff bit_push_bit_iff Parity.bit_push_bit_iff bit_take_bit_iff ac_simps exp_eq_zero_iff not_le)
  next
    case False
    then show ?thesis
      by (simp add: not_le bit_unsigned_iff bit_push_bit_iff Parity.bit_push_bit_iff bit_take_bit_iff)
  qed
qed

lemma unsigned_take_bit_eq:
  \<open>unsigned (take_bit n w) = take_bit n (unsigned w)\<close>
  for w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff bit_take_bit_iff Parity.bit_take_bit_iff)

end

context semiring_bit_operations
begin

lemma unsigned_and_eq:
  \<open>unsigned (v AND w) = unsigned v AND unsigned w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff bit_and_iff Bit_Operations.bit_and_iff)

lemma unsigned_or_eq:
  \<open>unsigned (v OR w) = unsigned v OR unsigned w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff bit_or_iff Bit_Operations.bit_or_iff)

lemma unsigned_xor_eq:
  \<open>unsigned (v XOR w) = unsigned v XOR unsigned w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_unsigned_iff bit_xor_iff Bit_Operations.bit_xor_iff)

end

context ring_bit_operations
begin

lemma unsigned_not_eq:
  \<open>unsigned (NOT w) = take_bit LENGTH('b) (NOT (unsigned w))\<close>
  for w :: \<open>'b::len word\<close>
  by (rule bit_eqI)
    (simp add: bit_unsigned_iff bit_take_bit_iff bit_not_iff Bit_Operations.bit_not_iff exp_eq_zero_iff not_le)

end

lemma unsigned_of_nat [simp]:
  \<open>unsigned (word_of_nat n :: 'a::len word) = of_nat (take_bit LENGTH('a) n)\<close>
  by transfer (simp add: nat_eq_iff take_bit_of_nat)

lemma unsigned_of_int [simp]:
  \<open>unsigned (word_of_int n :: 'a::len word) = of_int (take_bit LENGTH('a) n)\<close>
  by transfer (simp add: nat_eq_iff take_bit_of_nat)

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


subsubsection \<open>Generic signed conversion\<close>

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

context ring_bit_operations
begin

lemma bit_signed_iff:
  \<open>bit (signed w) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> bit w (min (LENGTH('b) - Suc 0) n)\<close>
  for w :: \<open>'b::len word\<close>
  by (transfer fixing: bit) (auto simp add: bit_of_int_iff bit_signed_take_bit_iff min_def)

lemma signed_push_bit_eq:
  \<open>signed (push_bit n w) = take_bit (LENGTH('b) - Suc 0) (push_bit n (signed w))
    OR of_bool (n < LENGTH('b) \<and> bit w (LENGTH('b) - Suc n)) * NOT (mask (LENGTH('b) - Suc 0))\<close>
  for w :: \<open>'b::len word\<close>
proof (rule bit_eqI)
  fix m
  assume \<open>2 ^ m \<noteq> 0\<close>
  define q where \<open>q = LENGTH('b) - Suc 0\<close>
  then have *: \<open>LENGTH('b) = Suc q\<close>
    by simp
  show \<open>bit (signed (push_bit n w)) m \<longleftrightarrow>
    bit (take_bit (LENGTH('b) - Suc 0) (push_bit n (signed w)) OR
      of_bool (n < LENGTH('b) \<and> bit w (LENGTH('b) - Suc n)) * NOT (mask (LENGTH('b) - Suc 0))) m\<close>
  proof (cases \<open>n \<le> m\<close>)
    case True
    with \<open>2 ^ m \<noteq> 0\<close> have \<open>2 ^ (m - n) \<noteq> 0\<close>
      by (metis (full_types) diff_add exp_add_not_zero_imp)
    with True show ?thesis
      by (auto simp add: * bit_signed_iff bit_push_bit_iff Parity.bit_push_bit_iff bit_or_iff bit_take_bit_iff bit_not_iff bit_mask_iff exp_eq_zero_iff min_def)
  next
    case False
    then show ?thesis
      by (simp add: * bit_signed_iff bit_push_bit_iff Parity.bit_push_bit_iff bit_or_iff bit_take_bit_iff bit_not_iff bit_mask_iff)
  qed
qed

lemma signed_take_bit_eq:
  \<open>signed (take_bit n w) = (if n < LENGTH('b) then take_bit n (signed w) else signed w)\<close>
  for w :: \<open>'b::len word\<close>
  by (transfer fixing: take_bit; cases \<open>LENGTH('b)\<close>)
    (auto simp add: signed_take_bit_take_bit take_bit_signed_take_bit take_bit_of_int min_def)

lemma signed_not_eq:
  \<open>signed (NOT w) = take_bit LENGTH('b) (NOT (signed w)) OR of_bool (bit (NOT (signed w)) LENGTH('b)) * NOT (mask LENGTH('b))\<close>
  for w :: \<open>'b::len word\<close>
proof (rule bit_eqI)
  fix n
  assume \<open>2 ^ n \<noteq> 0\<close>
  show \<open>bit (signed (NOT w)) n \<longleftrightarrow>
    bit (take_bit LENGTH('b) (NOT (signed w)) OR
    of_bool (bit (NOT (signed w)) LENGTH('b)) * NOT (mask LENGTH('b))) n\<close>
  proof (cases \<open>LENGTH('b) \<le> n\<close>)
    case False
    then show ?thesis
      by (auto simp add: bit_signed_iff bit_not_iff bit_or_iff bit_take_bit_iff bit_mask_iff Bit_Operations.bit_not_iff exp_eq_zero_iff)
  next
    case True
    moreover define q where \<open>q = n - LENGTH('b)\<close>
    ultimately have \<open>n = LENGTH('b) + q\<close>
      by simp
    with \<open>2 ^ n \<noteq> 0\<close> have \<open>2 ^ q \<noteq> 0\<close> \<open>2 ^ LENGTH('b) \<noteq> 0\<close>
      by (simp_all add: power_add) (use mult_not_zero in blast)+
    then show ?thesis
      by (simp add: bit_signed_iff bit_not_iff bit_or_iff bit_take_bit_iff bit_mask_iff Bit_Operations.bit_not_iff exp_eq_zero_iff min_def not_le not_less le_diff_conv le_Suc_eq)
  qed
qed

lemma signed_and_eq:
  \<open>signed (v AND w) = signed v AND signed w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_signed_iff bit_and_iff Bit_Operations.bit_and_iff)

lemma signed_or_eq:
  \<open>signed (v OR w) = signed v OR signed w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_signed_iff bit_or_iff Bit_Operations.bit_or_iff)

lemma signed_xor_eq:
  \<open>signed (v XOR w) = signed v XOR signed w\<close>
  for v w :: \<open>'b::len word\<close>
  by (rule bit_eqI) (simp add: bit_signed_iff bit_xor_iff Bit_Operations.bit_xor_iff)

end

lemma signed_of_nat [simp]:
  \<open>signed (word_of_nat n :: 'a::len word) = of_int (signed_take_bit (LENGTH('a) - Suc 0) (int n))\<close>
  by transfer simp

lemma signed_of_int [simp]:
  \<open>signed (word_of_int n :: 'a::len word) = of_int (signed_take_bit (LENGTH('a) - Suc 0) n)\<close>
  by transfer simp


subsubsection \<open>Important special cases\<close>

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

lemma of_nat_unat [simp]:
  \<open>of_nat (unat w) = unsigned w\<close>
  by transfer simp

lemma of_int_uint [simp]:
  \<open>of_int (uint w) = unsigned w\<close>
  by transfer simp

lemma unat_div_distrib:
  \<open>unat (v div w) = unat v div unat w\<close>
proof transfer
  fix k l
  have \<open>nat (take_bit LENGTH('a) k) div nat (take_bit LENGTH('a) l) \<le> nat (take_bit LENGTH('a) k)\<close>
    by (rule div_le_dividend)
  also have \<open>nat (take_bit LENGTH('a) k) < 2 ^ LENGTH('a)\<close>
    by (simp add: nat_less_iff take_bit_int_less_exp)
  finally show \<open>(nat \<circ> take_bit LENGTH('a)) (take_bit LENGTH('a) k div take_bit LENGTH('a) l) =
    (nat \<circ> take_bit LENGTH('a)) k div (nat \<circ> take_bit LENGTH('a)) l\<close>
    by (simp add: nat_take_bit_eq div_int_pos_iff nat_div_distrib take_bit_eq_self)
qed

lemma unat_mod_distrib:
  \<open>unat (v mod w) = unat v mod unat w\<close>
proof transfer
  fix k l
  have \<open>nat (take_bit LENGTH('a) k) mod nat (take_bit LENGTH('a) l) \<le> nat (take_bit LENGTH('a) k)\<close>
    by (rule mod_less_eq_dividend)
  also have \<open>nat (take_bit LENGTH('a) k) < 2 ^ LENGTH('a)\<close>
    by (simp add: nat_less_iff take_bit_int_less_exp)
  finally show \<open>(nat \<circ> take_bit LENGTH('a)) (take_bit LENGTH('a) k mod take_bit LENGTH('a) l) =
    (nat \<circ> take_bit LENGTH('a)) k mod (nat \<circ> take_bit LENGTH('a)) l\<close>
    by (simp add: nat_take_bit_eq mod_int_pos_iff less_le nat_mod_distrib take_bit_eq_self)
qed

lemma uint_div_distrib:
  \<open>uint (v div w) = uint v div uint w\<close>
proof -
  have \<open>int (unat (v div w)) = int (unat v div unat w)\<close>
    by (simp add: unat_div_distrib)
  then show ?thesis
    by (simp add: of_nat_div)
qed

lemma uint_mod_distrib:
  \<open>uint (v mod w) = uint v mod uint w\<close>
proof -
  have \<open>int (unat (v mod w)) = int (unat v mod unat w)\<close>
    by (simp add: unat_mod_distrib)
  then show ?thesis
    by (simp add: of_nat_mod)
qed

lemma of_int_sint [simp]:
  \<open>of_int (sint a) = signed a\<close>
  by transfer (simp_all add: take_bit_signed_take_bit)

lemma sint_not_eq:
  \<open>sint (NOT w) = signed_take_bit LENGTH('a) (NOT (sint w))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: signed_not_eq signed_take_bit_unfold)

lemma sint_push_bit_eq:
  \<open>signed (push_bit n w) = signed_take_bit (LENGTH('a) - 1) (push_bit n (signed w))\<close>
  for w :: \<open>'a::len word\<close>
  by (transfer fixing: n; cases \<open>LENGTH('a)\<close>)
     (auto simp add: signed_take_bit_def bit_concat_bit_iff bit_push_bit_iff bit_take_bit_iff bit_or_iff le_diff_conv2,
        auto simp add: take_bit_push_bit not_less concat_bit_eq_iff take_bit_concat_bit_eq le_diff_conv2)

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
    (simp_all add: signed_take_bit_eq signed_take_bit_unfold take_bit_int_less_exp not_eq_complement mask_eq_exp_minus_1 OR_upper)

end
