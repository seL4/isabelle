(*  Author:     Jeremy Dawson, NICTA
*)

section \<open>Operation variants with traditional syntax\<close>

theory Traditional_Syntax
  imports Word
begin

class semiring_bit_syntax = semiring_bit_shifts
begin

definition test_bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool\<close>  (infixl "!!" 100)
  where test_bit_eq_bit: \<open>test_bit = bit\<close>

definition shiftl :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl "<<" 55)
  where shiftl_eq_push_bit: \<open>a << n = push_bit n a\<close>

definition shiftr :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl ">>" 55)
  where shiftr_eq_drop_bit: \<open>a >> n = drop_bit n a\<close>

end

instance word :: (len) semiring_bit_syntax ..

context
  includes lifting_syntax
begin

lemma test_bit_word_transfer [transfer_rule]:
  \<open>(pcr_word ===> (=)) (\<lambda>k n. n < LENGTH('a) \<and> bit k n) (test_bit :: 'a::len word \<Rightarrow> _)\<close>
  by (unfold test_bit_eq_bit) transfer_prover

lemma shiftl_word_transfer [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (\<lambda>k n. push_bit n k) shiftl\<close>
  by (unfold shiftl_eq_push_bit) transfer_prover

lemma shiftr_word_transfer [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (\<lambda>k n. (drop_bit n \<circ> take_bit LENGTH('a)) k) (shiftr :: 'a::len word \<Rightarrow> _)\<close>
  by (unfold shiftr_eq_drop_bit) transfer_prover

end

lemma test_bit_word_eq:
  \<open>test_bit = (bit :: 'a::len word \<Rightarrow> _)\<close>
  by (fact test_bit_eq_bit)

lemma shiftl_word_eq:
  \<open>w << n = push_bit n w\<close> for w :: \<open>'a::len word\<close>
  by (fact shiftl_eq_push_bit)

lemma shiftr_word_eq:
  \<open>w >> n = drop_bit n w\<close> for w :: \<open>'a::len word\<close>
  by (fact shiftr_eq_drop_bit)

lemma test_bit_eq_iff: "test_bit u = test_bit v \<longleftrightarrow> u = v"
  for u v :: "'a::len word"
  by (simp add: bit_eq_iff test_bit_eq_bit fun_eq_iff)

lemma test_bit_size: "w !! n \<Longrightarrow> n < size w"
  for w :: "'a::len word"
  by transfer simp

lemma word_eq_iff: "x = y \<longleftrightarrow> (\<forall>n<LENGTH('a). x !! n = y !! n)" (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  for x y :: "'a::len word"
  by transfer (auto simp add: bit_eq_iff bit_take_bit_iff)

lemma word_eqI: "(\<And>n. n < size u \<longrightarrow> u !! n = v !! n) \<Longrightarrow> u = v"
  for u :: "'a::len word"
  by (simp add: word_size word_eq_iff)

lemma word_eqD: "u = v \<Longrightarrow> u !! x = v !! x"
  for u v :: "'a::len word"
  by simp

lemma test_bit_bin': "w !! n \<longleftrightarrow> n < size w \<and> bit (uint w) n"
  by transfer (simp add: bit_take_bit_iff)

lemmas test_bit_bin = test_bit_bin' [unfolded word_size]

lemma word_test_bit_def: 
  \<open>test_bit a = bit (uint a)\<close>
  by transfer (simp add: fun_eq_iff bit_take_bit_iff)

lemmas test_bit_def' = word_test_bit_def [THEN fun_cong]

lemma word_test_bit_transfer [transfer_rule]:
  "(rel_fun pcr_word (rel_fun (=) (=)))
    (\<lambda>x n. n < LENGTH('a) \<and> bit x n) (test_bit :: 'a::len word \<Rightarrow> _)"
  by (simp only: test_bit_eq_bit) transfer_prover

lemma test_bit_wi [simp]:
  "(word_of_int x :: 'a::len word) !! n \<longleftrightarrow> n < LENGTH('a) \<and> bit x n"
  by transfer simp

lemma word_ops_nth_size:
  "n < size x \<Longrightarrow>
    (x OR y) !! n = (x !! n | y !! n) \<and>
    (x AND y) !! n = (x !! n \<and> y !! n) \<and>
    (x XOR y) !! n = (x !! n \<noteq> y !! n) \<and>
    (NOT x) !! n = (\<not> x !! n)"
  for x :: "'a::len word"
  by transfer (simp add: bit_or_iff bit_and_iff bit_xor_iff bit_not_iff)

lemma word_ao_nth:
  "(x OR y) !! n = (x !! n | y !! n) \<and>
    (x AND y) !! n = (x !! n \<and> y !! n)"
  for x :: "'a::len word"
  by transfer (auto simp add: bit_or_iff bit_and_iff)

lemmas msb0 = len_gt_0 [THEN diff_Suc_less, THEN word_ops_nth_size [unfolded word_size]]
lemmas msb1 = msb0 [where i = 0]

lemma test_bit_numeral [simp]:
  "(numeral w :: 'a::len word) !! n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit (numeral w :: int) n"
  by transfer (rule refl)

lemma test_bit_neg_numeral [simp]:
  "(- numeral w :: 'a::len word) !! n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit (- numeral w :: int) n"
  by transfer (rule refl)

lemma test_bit_1 [simp]: "(1 :: 'a::len word) !! n \<longleftrightarrow> n = 0"
  by transfer (auto simp add: bit_1_iff) 

lemma nth_0 [simp]: "\<not> (0 :: 'a::len word) !! n"
  by transfer simp

lemma nth_minus1 [simp]: "(-1 :: 'a::len word) !! n \<longleftrightarrow> n < LENGTH('a)"
  by transfer simp

lemma shiftl1_code [code]:
  \<open>shiftl1 w = push_bit 1 w\<close>
  by transfer (simp add: ac_simps)

lemma uint_shiftr_eq:
  \<open>uint (w >> n) = uint w div 2 ^ n\<close>
  by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit min_def le_less less_diff_conv)

lemma shiftr1_code [code]:
  \<open>shiftr1 w = drop_bit 1 w\<close>
  by transfer (simp add: drop_bit_Suc)

lemma shiftl_def:
  \<open>w << n = (shiftl1 ^^ n) w\<close>
proof -
  have \<open>push_bit n = (((*) 2 ^^ n) :: int \<Rightarrow> int)\<close> for n
    by (induction n) (simp_all add: fun_eq_iff funpow_swap1, simp add: ac_simps)
  then show ?thesis
    by transfer simp
qed

lemma shiftr_def:
  \<open>w >> n = (shiftr1 ^^ n) w\<close>
proof -
  have \<open>shiftr1 ^^ n = (drop_bit n :: 'a word \<Rightarrow> 'a word)\<close>
    apply (induction n)
    apply simp
    apply (simp only: shiftr1_eq_div_2 [abs_def] drop_bit_eq_div [abs_def] funpow_Suc_right)
    apply (use div_exp_eq [of _ 1, where ?'a = \<open>'a word\<close>] in simp)
    done
  then show ?thesis
    by (simp add: shiftr_eq_drop_bit)
qed

lemma bit_shiftl_word_iff:
  \<open>bit (w << m) n \<longleftrightarrow> m \<le> n \<and> n < LENGTH('a) \<and> bit w (n - m)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftl_word_eq bit_push_bit_iff exp_eq_zero_iff not_le)

lemma bit_shiftr_word_iff:
  \<open>bit (w >> m) n \<longleftrightarrow> bit w (m + n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftr_word_eq bit_drop_bit_eq)

lift_definition sshiftr :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>  (infixl \<open>>>>\<close> 55)
  is \<open>\<lambda>k n. take_bit LENGTH('a) (drop_bit n (signed_take_bit (LENGTH('a) - Suc 0) k))\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma sshiftr_eq [code]:
  \<open>w >>> n = signed_drop_bit n w\<close>
  by transfer simp

lemma sshiftr_eq_funpow_sshiftr1:
  \<open>w >>> n = (sshiftr1 ^^ n) w\<close>
  apply (rule sym)
  apply (simp add: sshiftr1_eq_signed_drop_bit_Suc_0 sshiftr_eq)
  apply (induction n)
   apply simp_all
  done

lemma uint_sshiftr_eq:
  \<open>uint (w >>> n) = take_bit LENGTH('a) (sint w div 2 ^  n)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp flip: drop_bit_eq_div)

lemma sshift1_code [code]:
  \<open>sshiftr1 w = signed_drop_bit 1 w\<close>
  by transfer (simp add: drop_bit_Suc)

lemma sshiftr_0 [simp]: "0 >>> n = 0"
  by transfer simp

lemma sshiftr_n1 [simp]: "-1 >>> n = -1"
  by transfer simp

lemma bit_sshiftr_word_iff:
  \<open>bit (w >>> m) n \<longleftrightarrow> bit w (if LENGTH('a) - m \<le> n \<and> n < LENGTH('a) then LENGTH('a) - 1 else (m + n))\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq bit_signed_take_bit_iff min_def not_le simp flip: bit_Suc)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma nth_sshiftr :
  "(w >>> m) !! n =
    (n < size w \<and> (if n + m \<ge> size w then w !! (size w - 1) else w !! (n + m)))"
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq bit_signed_take_bit_iff min_def not_le ac_simps)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma sshiftr_numeral [simp]:
  \<open>(numeral k >>> numeral n :: 'a::len word) =
    word_of_int (drop_bit (numeral n) (signed_take_bit (LENGTH('a) - 1) (numeral k)))\<close>
  apply (rule word_eqI)
  apply (cases \<open>LENGTH('a)\<close>)
   apply (simp_all add: word_size bit_drop_bit_eq nth_sshiftr bit_signed_take_bit_iff min_def not_le not_less less_Suc_eq_le ac_simps)
  done

lemma revcast_down_us [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_ucast_iff bit_sshiftr_word_iff ac_simps)
  done

lemma revcast_down_ss [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_scast_iff bit_sshiftr_word_iff ac_simps)
  done

lemma sshiftr_div_2n: "sint (w >>> n) = sint w div 2 ^ n"
  using sint_signed_drop_bit_eq [of n w]
  by (simp add: drop_bit_eq_div sshiftr_eq) 

lemmas lsb0 = len_gt_0 [THEN word_ops_nth_size [unfolded word_size]]

lemma nth_sint:
  fixes w :: "'a::len word"
  defines "l \<equiv> LENGTH('a)"
  shows "bit (sint w) n = (if n < l - 1 then w !! n else w !! (l - 1))"
  unfolding sint_uint l_def
  by (auto simp: bit_signed_take_bit_iff word_test_bit_def not_less min_def)

lemma test_bit_2p: "(word_of_int (2 ^ n)::'a::len word) !! m \<longleftrightarrow> m = n \<and> m < LENGTH('a)"
  by transfer (auto simp add: bit_exp_iff)

lemma nth_w2p: "((2::'a::len word) ^ n) !! m \<longleftrightarrow> m = n \<and> m < LENGTH('a::len)"
  by transfer (auto simp add: bit_exp_iff)

lemma bang_is_le: "x !! m \<Longrightarrow> 2 ^ m \<le> x"
  for x :: "'a::len word"
  apply (rule xtrans(3))
   apply (rule_tac [2] y = "x" in le_word_or2)
  apply (rule word_eqI)
  apply (auto simp add: word_ao_nth nth_w2p word_size)
  done

lemma mask_eq:
  \<open>mask n = (1 << n) - (1 :: 'a::len word)\<close>
  by transfer (simp add: mask_eq_exp_minus_1 push_bit_of_1) 

lemma nth_ucast: "(ucast w::'a::len word) !! n = (w !! n \<and> n < LENGTH('a))"
  by transfer (simp add: bit_take_bit_iff ac_simps)

lemma shiftl_0 [simp]: "(0::'a::len word) << n = 0"
  by transfer simp

lemma shiftr_0 [simp]: "(0::'a::len word) >> n = 0"
  by transfer simp

lemma nth_shiftl1: "shiftl1 w !! n \<longleftrightarrow> n < size w \<and> n > 0 \<and> w !! (n - 1)"
  by transfer (auto simp add: bit_double_iff)

lemma nth_shiftl': "(w << m) !! n \<longleftrightarrow> n < size w \<and> n >= m \<and> w !! (n - m)"
  for w :: "'a::len word"
  by transfer (auto simp add: bit_push_bit_iff)

lemmas nth_shiftl = nth_shiftl' [unfolded word_size]

lemma nth_shiftr1: "shiftr1 w !! n = w !! Suc n"
  by transfer (auto simp add: bit_take_bit_iff simp flip: bit_Suc)

lemma nth_shiftr: "(w >> m) !! n = w !! (n + m)"
  for w :: "'a::len word"
  apply (unfold shiftr_def)
  apply (induct "m" arbitrary: n)
   apply (auto simp add: nth_shiftr1)
  done

lemma nth_sshiftr1: "sshiftr1 w !! n = (if n = size w - 1 then w !! n else w !! Suc n)"
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_signed_take_bit_iff min_def simp flip: bit_Suc)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma shiftr_div_2n: "uint (shiftr w n) = uint w div 2 ^ n"
  by (fact uint_shiftr_eq)

lemma shiftl_rev: "shiftl w n = word_reverse (shiftr (word_reverse w) n)"
  by (induct n) (auto simp add: shiftl_def shiftr_def shiftl1_rev)

lemma rev_shiftl: "word_reverse w << n = word_reverse (w >> n)"
  by (simp add: shiftl_rev)

lemma shiftr_rev: "w >> n = word_reverse (word_reverse w << n)"
  by (simp add: rev_shiftl)

lemma rev_shiftr: "word_reverse w >> n = word_reverse (w << n)"
  by (simp add: shiftr_rev)

lemma shiftl_numeral [simp]:
  \<open>numeral k << numeral l = (push_bit (numeral l) (numeral k) :: 'a::len word)\<close>
  by (fact shiftl_word_eq)

lemma shiftl_zero_size: "size x \<le> n \<Longrightarrow> x << n = 0"
  for x :: "'a::len word"
  apply transfer
  apply (simp add: take_bit_push_bit)
  done

lemma shiftl_t2n: "shiftl w n = 2 ^ n * w"
  for w :: "'a::len word"
  by (induct n) (auto simp: shiftl_def shiftl1_2t)

lemma shiftr_numeral [simp]:
  \<open>(numeral k >> numeral n :: 'a::len word) = drop_bit (numeral n) (numeral k)\<close>
  by (fact shiftr_word_eq)

lemma nth_mask [simp]:
  \<open>(mask n :: 'a::len word) !! i \<longleftrightarrow> i < n \<and> i < size (mask n :: 'a word)\<close>
  by (auto simp add: test_bit_word_eq word_size Word.bit_mask_iff)

lemma slice_shiftr: "slice n w = ucast (w >> n)"
  apply (rule bit_word_eqI)
  apply (cases \<open>n \<le> LENGTH('b)\<close>)
   apply (auto simp add: bit_slice_iff bit_ucast_iff bit_shiftr_word_iff ac_simps
    dest: bit_imp_le_length)
  done

lemma nth_slice: "(slice n w :: 'a::len word) !! m = (w !! (m + n) \<and> m < LENGTH('a))"
  by (simp add: slice_shiftr nth_ucast nth_shiftr)

lemma revcast_down_uu [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_ucast_iff bit_shiftr_word_iff ac_simps)
  done

lemma revcast_down_su [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_scast_iff bit_shiftr_word_iff ac_simps)
  done

lemma cast_down_rev [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> uc w = revcast (w << n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_ucast_iff bit_shiftl_word_iff)
  done

lemma revcast_up [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc + n = target_size rc \<Longrightarrow>
    rc w = (ucast w :: 'a::len word) << n"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_ucast_iff bit_shiftl_word_iff)
  apply auto
  apply (metis add.commute add_diff_cancel_right)
  apply (metis diff_add_inverse2 diff_diff_add)
  done

lemmas rc1 = revcast_up [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]
lemmas rc2 = revcast_down_uu [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]

lemmas ucast_up =
  rc1 [simplified rev_shiftr [symmetric] revcast_ucast [symmetric]]
lemmas ucast_down =
  rc2 [simplified rev_shiftr revcast_ucast [symmetric]]

\<comment> \<open>problem posed by TPHOLs referee:
      criterion for overflow of addition of signed integers\<close>

lemma sofl_test:
  \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (x + y XOR x) AND (x + y XOR y) >> (size x - 1) = 0\<close>
  for x y :: \<open>'a::len word\<close>
proof -
  obtain n where n: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  have *: \<open>sint x + sint y + 2 ^ Suc n > signed_take_bit n (sint x + sint y) \<Longrightarrow> sint x + sint y \<ge> - (2 ^ n)\<close>
    \<open>signed_take_bit n (sint x + sint y) > sint x + sint y - 2 ^ Suc n \<Longrightarrow> 2 ^ n > sint x + sint y\<close>
    using signed_take_bit_int_greater_eq [of \<open>sint x + sint y\<close> n] signed_take_bit_int_less_eq [of n \<open>sint x + sint y\<close>]
    by (auto intro: ccontr)
  have \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (sint (x + y) < 0 \<longleftrightarrow> sint x < 0) \<or>
    (sint (x + y) < 0 \<longleftrightarrow> sint y < 0)\<close>
    using sint_less [of x] sint_greater_eq [of x] sint_less [of y] sint_greater_eq [of y]
    signed_take_bit_int_eq_self [of \<open>LENGTH('a) - 1\<close> \<open>sint x + sint y\<close>]
    apply (auto simp add: not_less)
       apply (unfold sint_word_ariths)
       apply (subst signed_take_bit_int_eq_self)
         prefer 4
       apply (subst signed_take_bit_int_eq_self)
         prefer 7
       apply (subst signed_take_bit_int_eq_self)
         prefer 10
             apply (subst signed_take_bit_int_eq_self)
       apply (auto simp add: signed_take_bit_int_eq_self signed_take_bit_eq_take_bit_minus take_bit_Suc_from_most n not_less intro!: *)
    done
  then show ?thesis
    apply (simp only: One_nat_def word_size shiftr_word_eq drop_bit_eq_zero_iff_not_bit_last bit_and_iff bit_xor_iff)
    apply (simp add: bit_last_iff)
    done
qed

lemma shiftr_zero_size: "size x \<le> n \<Longrightarrow> x >> n = 0"
  for x :: "'a :: len word"
  by (rule word_eqI) (auto simp add: nth_shiftr dest: test_bit_size)

lemma test_bit_cat [OF refl]:
  "wc = word_cat a b \<Longrightarrow> wc !! n = (n < size wc \<and>
    (if n < size b then b !! n else a !! (n - size b)))"
  apply (simp add: word_size not_less; transfer)
       apply (auto simp add: bit_concat_bit_iff bit_take_bit_iff)
  done

\<comment> \<open>keep quantifiers for use in simplification\<close>
lemma test_bit_split':
  "word_split c = (a, b) \<longrightarrow>
    (\<forall>n m.
      b !! n = (n < size b \<and> c !! n) \<and>
      a !! m = (m < size a \<and> c !! (m + size b)))"
  by (auto simp add: word_split_bin' test_bit_bin bit_unsigned_iff word_size
    bit_drop_bit_eq ac_simps exp_eq_zero_iff
    dest: bit_imp_le_length)

lemma test_bit_split:
  "word_split c = (a, b) \<Longrightarrow>
    (\<forall>n::nat. b !! n \<longleftrightarrow> n < size b \<and> c !! n) \<and>
    (\<forall>m::nat. a !! m \<longleftrightarrow> m < size a \<and> c !! (m + size b))"
  by (simp add: test_bit_split')

lemma test_bit_split_eq:
  "word_split c = (a, b) \<longleftrightarrow>
    ((\<forall>n::nat. b !! n = (n < size b \<and> c !! n)) \<and>
     (\<forall>m::nat. a !! m = (m < size a \<and> c !! (m + size b))))"
  apply (rule_tac iffI)
   apply (rule_tac conjI)
    apply (erule test_bit_split [THEN conjunct1])
   apply (erule test_bit_split [THEN conjunct2])
  apply (case_tac "word_split c")
  apply (frule test_bit_split)
  apply (erule trans)
  apply (fastforce intro!: word_eqI simp add: word_size)
  done

lemma test_bit_rcat:
  "sw = size (hd wl) \<Longrightarrow> rc = word_rcat wl \<Longrightarrow> rc !! n =
    (n < size rc \<and> n div sw < size wl \<and> (rev wl) ! (n div sw) !! (n mod sw))"
  for wl :: "'a::len word list"
  by (simp add: word_size word_rcat_def foldl_map rev_map bit_horner_sum_uint_exp_iff)
    (simp add: test_bit_eq_bit)

lemmas test_bit_cong = arg_cong [where f = "test_bit", THEN fun_cong]

lemma max_test_bit: "(max_word::'a::len word) !! n \<longleftrightarrow> n < LENGTH('a)"
  by (fact nth_minus1)

lemma shiftr_x_0 [iff]: "x >> 0 = x"
  for x :: "'a::len word"
  by transfer simp

lemma shiftl_x_0 [simp]: "x << 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftl_t2n)

lemma shiftl_1 [simp]: "(1::'a::len word) << n = 2^n"
  by (simp add: shiftl_t2n)

lemma shiftr_1[simp]: "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (induct n) (auto simp: shiftr_def)

lemma map_nth_0 [simp]: "map ((!!) (0::'a::len word)) xs = replicate (length xs) False"
  by (induct xs) auto

lemma word_and_1:
  "n AND 1 = (if n !! 0 then 1 else 0)" for n :: "_ word"
  by (rule bit_word_eqI) (auto simp add: bit_and_iff test_bit_eq_bit bit_1_iff intro: gr0I)

lemma test_bit_1' [simp]:
  "(1 :: 'a :: len word) !! n \<longleftrightarrow> 0 < LENGTH('a) \<and> n = 0"
  by simp

lemma shiftl0:
  "x << 0 = (x :: 'a :: len word)"
  by (fact shiftl_x_0)

setup \<open>
  Context.theory_map (fold SMT_Word.add_word_shift' [
    (\<^term>\<open>shiftl :: 'a::len word \<Rightarrow> _\<close>, "bvshl"),
    (\<^term>\<open>shiftr :: 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>sshiftr :: 'a::len word \<Rightarrow> _\<close>, "bvashr")
  ])
\<close>

end
