(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for algebraically founded bit word types\<close>

theory Word
  imports
    Main
    "HOL-Library.Type_Length"
    "HOL-ex.Bit_Operations"
begin

subsection \<open>Preliminaries\<close>

definition signed_take_bit :: "nat \<Rightarrow> int \<Rightarrow> int"
  where signed_take_bit_eq_take_bit:
    "signed_take_bit n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n"

lemma signed_take_bit_eq_take_bit':
  "signed_take_bit (n - Suc 0) k = take_bit n (k + 2 ^ (n - 1)) - 2 ^ (n - 1)" if "n > 0"
  using that by (simp add: signed_take_bit_eq_take_bit)

lemma signed_take_bit_0 [simp]:
  "signed_take_bit 0 k = - (k mod 2)"
proof (cases "even k")
  case True
  then have "odd (k + 1)"
    by simp
  then have "(k + 1) mod 2 = 1"
    by (simp add: even_iff_mod_2_eq_zero)
  with True show ?thesis
    by (simp add: signed_take_bit_eq_take_bit)
next
  case False
  then show ?thesis
    by (simp add: signed_take_bit_eq_take_bit odd_iff_mod_2_eq_one)
qed

lemma signed_take_bit_Suc [simp]:
  "signed_take_bit (Suc n) k = signed_take_bit n (k div 2) * 2 + k mod 2"
  by (simp add: odd_iff_mod_2_eq_one signed_take_bit_eq_take_bit algebra_simps)

lemma signed_take_bit_of_0 [simp]:
  "signed_take_bit n 0 = 0"
  by (simp add: signed_take_bit_eq_take_bit take_bit_eq_mod)

lemma signed_take_bit_of_minus_1 [simp]:
  "signed_take_bit n (- 1) = - 1"
  by (induct n) simp_all

lemma signed_take_bit_eq_iff_take_bit_eq:
  "signed_take_bit (n - Suc 0) k = signed_take_bit (n - Suc 0) l \<longleftrightarrow> take_bit n k = take_bit n l" (is "?P \<longleftrightarrow> ?Q")
  if "n > 0"
proof -
  from that obtain m where m: "n = Suc m"
    by (cases n) auto
  show ?thesis
  proof
    assume ?Q
    have "take_bit (Suc m) (k + 2 ^ m) =
      take_bit (Suc m) (take_bit (Suc m) k + take_bit (Suc m) (2 ^ m))"
      by (simp only: take_bit_add)
    also have "\<dots> =
      take_bit (Suc m) (take_bit (Suc m) l + take_bit (Suc m) (2 ^ m))"
      by (simp only: \<open>?Q\<close> m [symmetric])
    also have "\<dots> = take_bit (Suc m) (l + 2 ^ m)"
      by (simp only: take_bit_add)
    finally show ?P
      by (simp only: signed_take_bit_eq_take_bit m) simp
  next
    assume ?P
    with that have "(k + 2 ^ (n - Suc 0)) mod 2 ^ n = (l + 2 ^ (n - Suc 0)) mod 2 ^ n"
      by (simp add: signed_take_bit_eq_take_bit' take_bit_eq_mod)
    then have "(i + (k + 2 ^ (n - Suc 0))) mod 2 ^ n = (i + (l + 2 ^ (n - Suc 0))) mod 2 ^ n" for i
      by (metis mod_add_eq)
    then have "k mod 2 ^ n = l mod 2 ^ n"
      by (metis add_diff_cancel_right' uminus_add_conv_diff)
    then show ?Q
      by (simp add: take_bit_eq_mod)
  qed
qed


subsection \<open>Bit strings as quotient type\<close>

subsubsection \<open>Basic properties\<close>

quotient_type (overloaded) 'a word = int / "\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a::len0) l"
  by (auto intro!: equivpI reflpI sympI transpI)

instantiation word :: (len0) "{semiring_numeral, comm_semiring_0, comm_ring}"
begin

lift_definition zero_word :: "'a word"
  is 0
  .

lift_definition one_word :: "'a word"
  is 1
  .

lift_definition plus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is plus
  by (subst take_bit_add [symmetric]) (simp add: take_bit_add)

lift_definition uminus_word :: "'a word \<Rightarrow> 'a word"
  is uminus
  by (subst take_bit_minus [symmetric]) (simp add: take_bit_minus)

lift_definition minus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is minus
  by (subst take_bit_diff [symmetric]) (simp add: take_bit_diff)

lift_definition times_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is times
  by (auto simp add: take_bit_eq_mod intro: mod_mult_cong)

instance
  by standard (transfer; simp add: algebra_simps)+

end

instance word :: (len) comm_ring_1
  by standard (transfer; simp)+

quickcheck_generator word
  constructors:
    "zero_class.zero :: ('a::len0) word",
    "numeral :: num \<Rightarrow> ('a::len0) word",
    "uminus :: ('a::len0) word \<Rightarrow> ('a::len0) word"

context
  includes lifting_syntax
  notes power_transfer [transfer_rule]
begin

lemma power_transfer_word [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (^) (^)\<close>
  by transfer_prover

end


subsubsection \<open>Conversions\<close>

context
  includes lifting_syntax
  notes 
    transfer_rule_of_bool [transfer_rule]
    transfer_rule_numeral [transfer_rule]
    transfer_rule_of_nat [transfer_rule]
    transfer_rule_of_int [transfer_rule]
begin

lemma [transfer_rule]:
  "((=) ===> (pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> bool)) of_bool of_bool"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> (pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> bool)) numeral numeral"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> pcr_word) int of_nat"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> pcr_word) (\<lambda>k. k) of_int"
proof -
  have "((=) ===> pcr_word) of_int of_int"
    by transfer_prover
  then show ?thesis by (simp add: id_def)
qed

end

lemma abs_word_eq:
  "abs_word = of_int"
  by (rule ext) (transfer, rule)

context semiring_1
begin

lift_definition unsigned :: "'b::len0 word \<Rightarrow> 'a"
  is "of_nat \<circ> nat \<circ> take_bit LENGTH('b)"
  by simp

lemma unsigned_0 [simp]:
  "unsigned 0 = 0"
  by transfer simp

end

context semiring_char_0
begin

lemma word_eq_iff_unsigned:
  "a = b \<longleftrightarrow> unsigned a = unsigned b"
  by safe (transfer; simp add: eq_nat_nat_iff)

end

instantiation word :: (len0) equal
begin

definition equal_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  where "equal_word a b \<longleftrightarrow> (unsigned a :: int) = unsigned b"

instance proof
  fix a b :: "'a word"
  show "HOL.equal a b \<longleftrightarrow> a = b"
    using word_eq_iff_unsigned [of a b] by (auto simp add: equal_word_def)
qed

end

context ring_1
begin

lift_definition signed :: "'b::len word \<Rightarrow> 'a"
  is "of_int \<circ> signed_take_bit (LENGTH('b) - 1)"
  by (simp add: signed_take_bit_eq_iff_take_bit_eq [symmetric])

lemma signed_0 [simp]:
  "signed 0 = 0"
  by transfer simp

end

lemma unsigned_of_nat [simp]:
  "unsigned (of_nat n :: 'a word) = take_bit LENGTH('a::len) n"
  by transfer (simp add: nat_eq_iff take_bit_eq_mod zmod_int)

lemma of_nat_unsigned [simp]:
  "of_nat (unsigned a) = a"
  by transfer simp

lemma of_int_unsigned [simp]:
  "of_int (unsigned a) = a"
  by transfer simp

lemma unsigned_nat_less:
  \<open>unsigned a < (2 ^ LENGTH('a) :: nat)\<close> for a :: \<open>'a::len0 word\<close>
  by transfer (simp add: take_bit_eq_mod)

lemma unsigned_int_less:
  \<open>unsigned a < (2 ^ LENGTH('a) :: int)\<close> for a :: \<open>'a::len0 word\<close>
  by transfer (simp add: take_bit_eq_mod)

context ring_char_0
begin

lemma word_eq_iff_signed:
  "a = b \<longleftrightarrow> signed a = signed b"
  by safe (transfer; auto simp add: signed_take_bit_eq_iff_take_bit_eq)

end

lemma signed_of_int [simp]:
  "signed (of_int k :: 'a word) = signed_take_bit (LENGTH('a::len) - 1) k"
  by transfer simp

lemma of_int_signed [simp]:
  "of_int (signed a) = a"
  by transfer (simp add: signed_take_bit_eq_take_bit take_bit_eq_mod mod_simps)


subsubsection \<open>Properties\<close>

lemma exp_eq_zero_iff:
  \<open>(2 :: 'a::len word) ^ n = 0 \<longleftrightarrow> LENGTH('a) \<le> n\<close>
  by transfer simp


subsubsection \<open>Division\<close>

instantiation word :: (len0) modulo
begin

lift_definition divide_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. take_bit LENGTH('a) a div take_bit LENGTH('a) b"
  by simp

lift_definition modulo_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. take_bit LENGTH('a) a mod take_bit LENGTH('a) b"
  by simp

instance ..

end

lemma zero_word_div_eq [simp]:
  \<open>0 div a = 0\<close> for a :: \<open>'a::len0 word\<close>
  by transfer simp

lemma div_zero_word_eq [simp]:
  \<open>a div 0 = 0\<close> for a :: \<open>'a::len0 word\<close>
  by transfer simp

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  "(pcr_word ===> (\<longleftrightarrow>)) even ((dvd) 2 :: 'a::len word \<Rightarrow> bool)"
proof -
  have even_word_unfold: "even k \<longleftrightarrow> (\<exists>l. take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l))" (is "?P \<longleftrightarrow> ?Q")
    for k :: int
  proof
    assume ?P
    then show ?Q
      by auto
  next
    assume ?Q
    then obtain l where "take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l)" ..
    then have "even (take_bit LENGTH('a) k)"
      by simp
    then show ?P
      by simp
  qed
  show ?thesis by (simp only: even_word_unfold [abs_def] dvd_def [where ?'a = "'a word", abs_def])
    transfer_prover
qed

end

instance word :: (len) semiring_modulo
proof
  show "a div b * b + a mod b = a" for a b :: "'a word"
  proof transfer
    fix k l :: int
    define r :: int where "r = 2 ^ LENGTH('a)"
    then have r: "take_bit LENGTH('a) k = k mod r" for k
      by (simp add: take_bit_eq_mod)
    have "k mod r = ((k mod r) div (l mod r) * (l mod r)
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: div_mult_mod_eq)
    also have "... = (((k mod r) div (l mod r) * (l mod r)) mod r
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_add_left_eq)
    also have "... = (((k mod r) div (l mod r) * l) mod r
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_mult_right_eq)
    finally have "k mod r = ((k mod r) div (l mod r) * l
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_simps)
    with r show "take_bit LENGTH('a) (take_bit LENGTH('a) k div take_bit LENGTH('a) l * l
      + take_bit LENGTH('a) k mod take_bit LENGTH('a) l) = take_bit LENGTH('a) k"
      by simp
  qed
qed

instance word :: (len) semiring_parity
proof
  show "\<not> 2 dvd (1::'a word)"
    by transfer simp
  show even_iff_mod_2_eq_0: "2 dvd a \<longleftrightarrow> a mod 2 = 0"
    for a :: "'a word"
    by transfer (simp_all add: mod_2_eq_odd)
  show "\<not> 2 dvd a \<longleftrightarrow> a mod 2 = 1"
    for a :: "'a word"
    by transfer (simp_all add: mod_2_eq_odd)
qed


subsubsection \<open>Orderings\<close>

instantiation word :: (len0) linorder
begin

lift_definition less_eq_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a \<le> take_bit LENGTH('a) b"
  by simp

lift_definition less_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a < take_bit LENGTH('a) b"
  by simp

instance
  by standard (transfer; auto)+

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

lemma word_greater_zero_iff:
  \<open>a > 0 \<longleftrightarrow> a \<noteq> 0\<close> for a :: \<open>'a::len0 word\<close>
  by transfer (simp add: less_le)

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


subsection \<open>Bit structure on \<^typ>\<open>'a word\<close>\<close>

lemma word_bit_induct [case_names zero even odd]:
  \<open>P a\<close> if word_zero: \<open>P 0\<close>
    and word_even: \<open>\<And>a. P a \<Longrightarrow> 0 < a \<Longrightarrow> a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> P (2 * a)\<close>
    and word_odd: \<open>\<And>a. P a \<Longrightarrow> a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> P (1 + 2 * a)\<close>
  for P and a :: \<open>'a::len word\<close>
proof -
  define m :: nat where \<open>m = LENGTH('a) - 1\<close>
  then have l: \<open>LENGTH('a) = Suc m\<close>
    by simp
  define n :: nat where \<open>n = unsigned a\<close>
  then have \<open>n < 2 ^ LENGTH('a)\<close>
    by (simp add: unsigned_nat_less)
  then have \<open>n < 2 * 2 ^ m\<close>
    by (simp add: l)
  then have \<open>P (of_nat n)\<close>
  proof (induction n rule: nat_bit_induct)
    case zero
    show ?case
      by simp (rule word_zero)
  next
    case (even n)
    then have \<open>n < 2 ^ m\<close>
      by simp
    with even.IH have \<open>P (of_nat n)\<close>
      by simp
    moreover from \<open>n < 2 ^ m\<close> even.hyps have \<open>0 < (of_nat n :: 'a word)\<close>
      by (auto simp add: word_greater_zero_iff of_nat_word_eq_0_iff l)
    moreover from \<open>n < 2 ^ m\<close> have \<open>(of_nat n :: 'a word) < 2 ^ (LENGTH('a) - 1)\<close>
      using of_nat_word_less_iff [where ?'a = 'a, of n \<open>2 ^ m\<close>]
      by (cases \<open>m = 0\<close>) (simp_all add: not_less take_bit_eq_self ac_simps l)
    ultimately have \<open>P (2 * of_nat n)\<close>
      by (rule word_even)
    then show ?case
      by simp
  next
    case (odd n)
    then have \<open>Suc n \<le> 2 ^ m\<close>
      by simp
    with odd.IH have \<open>P (of_nat n)\<close>
      by simp
    moreover from \<open>Suc n \<le> 2 ^ m\<close> have \<open>(of_nat n :: 'a word) < 2 ^ (LENGTH('a) - 1)\<close>
      using of_nat_word_less_iff [where ?'a = 'a, of n \<open>2 ^ m\<close>]
      by (cases \<open>m = 0\<close>) (simp_all add: not_less take_bit_eq_self ac_simps l)
    ultimately have \<open>P (1 + 2 * of_nat n)\<close>
      by (rule word_odd)
    then show ?case
      by simp
  qed
  then show ?thesis
    by (simp add: n_def)
qed

lemma bit_word_half_eq:
  \<open>(of_bool b + a * 2) div 2 = a\<close>
    if \<open>a < 2 ^ (LENGTH('a) - Suc 0)\<close>
    for a :: \<open>'a::len word\<close>
proof (cases \<open>2 \<le> LENGTH('a::len)\<close>)
  case False
  have \<open>of_bool (odd k) < (1 :: int) \<longleftrightarrow> even k\<close> for k :: int
    by auto
  with False that show ?thesis
    by (auto; transfer) simp_all
next
  case True
  obtain n where length: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  show ?thesis proof (cases b)
    case False
    moreover have \<open>a * 2 div 2 = a\<close>
    using that proof transfer
      fix k :: int
      from length have \<open>k * 2 mod 2 ^ LENGTH('a) = (k mod 2 ^ n) * 2\<close>
        by simp
      moreover assume \<open>take_bit LENGTH('a) k < take_bit LENGTH('a) (2 ^ (LENGTH('a) - Suc 0))\<close>
      with \<open>LENGTH('a) = Suc n\<close>
      have \<open>k mod 2 ^ LENGTH('a) = k mod 2 ^ n\<close>
        by (simp add: take_bit_eq_mod divmod_digit_0)
      ultimately have \<open>take_bit LENGTH('a) (k * 2) = take_bit LENGTH('a) k * 2\<close>
        by (simp add: take_bit_eq_mod)
      with True show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (k * 2) div take_bit LENGTH('a) 2)
        = take_bit LENGTH('a) k\<close>
        by simp
    qed
    ultimately show ?thesis
      by simp
  next
    case True
    moreover have \<open>(1 + a * 2) div 2 = a\<close>
    using that proof transfer
      fix k :: int
      from length have \<open>(1 + k * 2) mod 2 ^ LENGTH('a) = 1 + (k mod 2 ^ n) * 2\<close>
        using pos_zmod_mult_2 [of \<open>2 ^ n\<close> k] by (simp add: ac_simps)
      moreover assume \<open>take_bit LENGTH('a) k < take_bit LENGTH('a) (2 ^ (LENGTH('a) - Suc 0))\<close>
      with \<open>LENGTH('a) = Suc n\<close>
      have \<open>k mod 2 ^ LENGTH('a) = k mod 2 ^ n\<close>
        by (simp add: take_bit_eq_mod divmod_digit_0)
      ultimately have \<open>take_bit LENGTH('a) (1 + k * 2) = 1 + take_bit LENGTH('a) k * 2\<close>
        by (simp add: take_bit_eq_mod)
      with True show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (1 + k * 2) div take_bit LENGTH('a) 2)
        = take_bit LENGTH('a) k\<close>
        by auto
    qed
    ultimately show ?thesis
      by simp
  qed
qed

lemma even_mult_exp_div_word_iff:
  \<open>even (a * 2 ^ m div 2 ^ n) \<longleftrightarrow> \<not> (
    m \<le> n \<and>
    n < LENGTH('a) \<and> odd (a div 2 ^ (n - m)))\<close> for a :: \<open>'a::len word\<close>
  by transfer
    (auto simp flip: drop_bit_eq_div simp add: even_drop_bit_iff_not_bit bit_take_bit_iff,
      simp_all flip: push_bit_eq_mult add: bit_push_bit_iff_int)

instance word :: (len) semiring_bits
proof
  show \<open>P a\<close> if stable: \<open>\<And>a. a div 2 = a \<Longrightarrow> P a\<close>
    and rec: \<open>\<And>a b. P a \<Longrightarrow> (of_bool b + 2 * a) div 2 = a \<Longrightarrow> P (of_bool b + 2 * a)\<close>
  for P and a :: \<open>'a word\<close>
  proof (induction a rule: word_bit_induct)
    case zero
    from stable [of 0] show ?case
      by simp
  next
    case (even a)
    with rec [of a False] show ?case
      using bit_word_half_eq [of a False] by (simp add: ac_simps)
  next
    case (odd a)
    with rec [of a True] show ?case
      using bit_word_half_eq [of a True] by (simp add: ac_simps)
  qed
  show \<open>0 div a = 0\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>a div 1 = a\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>a mod b div b = 0\<close>
    for a b :: \<open>'a word\<close>
    apply transfer
    apply (simp add: take_bit_eq_mod)
    apply (subst (3) mod_pos_pos_trivial [of _ \<open>2 ^ LENGTH('a)\<close>])
      apply simp_all
     apply (metis le_less mod_by_0 pos_mod_conj zero_less_numeral zero_less_power)
    using pos_mod_bound [of \<open>2 ^ LENGTH('a)\<close>] apply simp
  proof -
    fix aa :: int and ba :: int
    have f1: "\<And>i n. (i::int) mod 2 ^ n = 0 \<or> 0 < i mod 2 ^ n"
      by (metis le_less take_bit_eq_mod take_bit_nonnegative)
    have "(0::int) < 2 ^ len_of (TYPE('a)::'a itself) \<and> ba mod 2 ^ len_of (TYPE('a)::'a itself) \<noteq> 0 \<or> aa mod 2 ^ len_of (TYPE('a)::'a itself) mod (ba mod 2 ^ len_of (TYPE('a)::'a itself)) < 2 ^ len_of (TYPE('a)::'a itself)"
      by (metis (no_types) mod_by_0 unique_euclidean_semiring_numeral_class.pos_mod_bound zero_less_numeral zero_less_power)
    then show "aa mod 2 ^ len_of (TYPE('a)::'a itself) mod (ba mod 2 ^ len_of (TYPE('a)::'a itself)) < 2 ^ len_of (TYPE('a)::'a itself)"
      using f1 by (meson le_less less_le_trans unique_euclidean_semiring_numeral_class.pos_mod_bound)
  qed
  show \<open>(1 + a) div 2 = a div 2\<close>
    if \<open>even a\<close>
    for a :: \<open>'a word\<close>
    using that by transfer (auto dest: le_Suc_ex)
  show \<open>(2 :: 'a word) ^ m div 2 ^ n = of_bool ((2 :: 'a word) ^ m \<noteq> 0 \<and> n \<le> m) * 2 ^ (m - n)\<close>
    for m n :: nat
    by transfer (simp, simp add: exp_div_exp_eq)
  show "a div 2 ^ m div 2 ^ n = a div 2 ^ (m + n)"
    for a :: "'a word" and m n :: nat
    apply transfer
    apply (auto simp add: not_less take_bit_drop_bit ac_simps simp flip: drop_bit_eq_div)
    apply (simp add: drop_bit_take_bit)
    done
  show "a mod 2 ^ m mod 2 ^ n = a mod 2 ^ min m n"
    for a :: "'a word" and m n :: nat
    by transfer (auto simp flip: take_bit_eq_mod simp add: ac_simps)
  show \<open>a * 2 ^ m mod 2 ^ n = a mod 2 ^ (n - m) * 2 ^ m\<close>
    if \<open>m \<le> n\<close> for a :: "'a word" and m n :: nat
    using that apply transfer
    apply (auto simp flip: take_bit_eq_mod)
           apply (auto simp flip: push_bit_eq_mult simp add: push_bit_take_bit split: split_min_lin)
    done
  show \<open>a div 2 ^ n mod 2 ^ m = a mod (2 ^ (n + m)) div 2 ^ n\<close>
    for a :: "'a word" and m n :: nat
    by transfer (auto simp add: not_less take_bit_drop_bit ac_simps simp flip: take_bit_eq_mod drop_bit_eq_div split: split_min_lin)
  show \<open>even ((2 ^ m - 1) div (2::'a word) ^ n) \<longleftrightarrow> 2 ^ n = (0::'a word) \<or> m \<le> n\<close>
    for m n :: nat
    by transfer (auto simp add: take_bit_of_mask even_mask_div_iff)
  show \<open>even (a * 2 ^ m div 2 ^ n) \<longleftrightarrow> n < m \<or> (2::'a word) ^ n = 0 \<or> m \<le> n \<and> even (a div 2 ^ (n - m))\<close>
    for a :: \<open>'a word\<close> and m n :: nat
  proof transfer
    show \<open>even (take_bit LENGTH('a) (k * 2 ^ m) div take_bit LENGTH('a) (2 ^ n)) \<longleftrightarrow>
      n < m
      \<or> take_bit LENGTH('a) ((2::int) ^ n) = take_bit LENGTH('a) 0
      \<or> (m \<le> n \<and> even (take_bit LENGTH('a) k div take_bit LENGTH('a) (2 ^ (n - m))))\<close>
    for m n :: nat and k l :: int
      by (auto simp flip: take_bit_eq_mod drop_bit_eq_div push_bit_eq_mult
        simp add: div_push_bit_of_1_eq_drop_bit drop_bit_take_bit drop_bit_push_bit_int [of n m])
  qed
qed

context
  includes lifting_syntax
begin

lemma transfer_rule_bit_word [transfer_rule]:
  \<open>((pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> bool) ===> (=)) (\<lambda>k n. n < LENGTH('a) \<and> bit k n) bit\<close>
proof -
  let ?t = \<open>\<lambda>a n. odd (take_bit LENGTH('a) a div take_bit LENGTH('a) ((2::int) ^ n))\<close>
  have \<open>((pcr_word :: int \<Rightarrow> 'a word \<Rightarrow> bool) ===> (=)) ?t bit\<close>
    by (unfold bit_def) transfer_prover
  also have \<open>?t = (\<lambda>k n. n < LENGTH('a) \<and> bit k n)\<close>
    by (simp add: fun_eq_iff bit_take_bit_iff flip: bit_def)
  finally show ?thesis .
qed

end

instantiation word :: (len) semiring_bit_shifts
begin

lift_definition push_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is push_bit
proof -
  show \<open>take_bit LENGTH('a) (push_bit n k) = take_bit LENGTH('a) (push_bit n l)\<close>
    if \<open>take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close> for k l :: int and n :: nat
  proof -
    from that
    have \<open>take_bit (LENGTH('a) - n) (take_bit LENGTH('a) k)
      = take_bit (LENGTH('a) - n) (take_bit LENGTH('a) l)\<close>
      by simp
    moreover have \<open>min (LENGTH('a) - n) LENGTH('a) = LENGTH('a) - n\<close>
      by simp
    ultimately show ?thesis
      by (simp add: take_bit_push_bit)
  qed
qed

lift_definition drop_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>n. drop_bit n \<circ> take_bit LENGTH('a)\<close>
  by (simp add: take_bit_eq_mod)

instance proof
  show \<open>push_bit n a = a * 2 ^ n\<close> for n :: nat and a :: "'a word"
    by transfer (simp add: push_bit_eq_mult)
  show \<open>drop_bit n a = a div 2 ^ n\<close> for n :: nat and a :: "'a word"
    by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit)
qed

end

instantiation word :: (len) ring_bit_operations
begin

lift_definition not_word :: "'a word \<Rightarrow> 'a word"
  is not
  by (simp add: take_bit_not_iff)

lift_definition and_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is \<open>and\<close>
  by simp

lift_definition or_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is or
  by simp

lift_definition xor_word ::  "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is xor
  by simp

instance proof
  fix a b :: \<open>'a word\<close> and n :: nat
  show \<open>- a = NOT (a - 1)\<close>
    by transfer (simp add: minus_eq_not_minus_1)
  show \<open>bit (NOT a) n \<longleftrightarrow> (2 :: 'a word) ^ n \<noteq> 0 \<and> \<not> bit a n\<close>
    by transfer (simp add: bit_not_iff)
  show \<open>bit (a AND b) n \<longleftrightarrow> bit a n \<and> bit b n\<close>
    by transfer (auto simp add: bit_and_iff)
  show \<open>bit (a OR b) n \<longleftrightarrow> bit a n \<or> bit b n\<close>
    by transfer (auto simp add: bit_or_iff)
  show \<open>bit (a XOR b) n \<longleftrightarrow> bit a n \<noteq> bit b n\<close>
    by transfer (auto simp add: bit_xor_iff)
qed

end

lifting_update word.lifting
lifting_forget word.lifting

end
