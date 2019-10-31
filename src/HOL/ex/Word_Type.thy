(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for algebraically founded bit word types\<close>

theory Word_Type
  imports
    Main
    "HOL-ex.Bit_Lists"
    "HOL-Library.Type_Length"
begin

subsection \<open>Preliminaries\<close>

lemma take_bit_uminus:
  "take_bit n (- (take_bit n k)) = take_bit n (- k)" for k :: int
  by (simp add: take_bit_eq_mod mod_minus_eq)

lemma take_bit_minus:
  "take_bit n (take_bit n k - take_bit n l) = take_bit n (k - l)" for k l :: int
  by (simp add: take_bit_eq_mod mod_diff_eq)

lemma take_bit_nonnegative [simp]:
  "take_bit n k \<ge> 0" for k :: int
  by (simp add: take_bit_eq_mod)

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
  by (subst take_bit_uminus [symmetric]) (simp add: take_bit_uminus)

lift_definition minus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is minus
  by (subst take_bit_minus [symmetric]) (simp add: take_bit_minus)

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
  notes transfer_rule_numeral [transfer_rule]
    transfer_rule_of_nat [transfer_rule]
    transfer_rule_of_int [transfer_rule]
begin

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

lemma length_cases:
  obtains (triv) "LENGTH('a::len) = 1" "take_bit LENGTH('a) 2 = (0 :: int)"
    | (take_bit_2) "take_bit LENGTH('a) 2 = (2 :: int)"
proof (cases "LENGTH('a) \<ge> 2")
  case False
  then have "LENGTH('a) = 1"
    by (auto simp add: not_le dest: less_2_cases)
  then have "take_bit LENGTH('a) 2 = (0 :: int)"
    by simp
  with \<open>LENGTH('a) = 1\<close> triv show ?thesis
    by simp
next
  case True
  then obtain n where "LENGTH('a) = Suc (Suc n)"
    by (auto dest: le_Suc_ex)
  then have "take_bit LENGTH('a) 2 = (2 :: int)"
    by simp
  with take_bit_2 show ?thesis
    by simp
qed


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
    by (transfer; cases rule: length_cases [where ?'a = 'a]) (simp_all add: mod_2_eq_odd)
  show "\<not> 2 dvd a \<longleftrightarrow> a mod 2 = 1"
    for a :: "'a word"
    by (transfer; cases rule: length_cases [where ?'a = 'a]) (simp_all add: mod_2_eq_odd)
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


subsection \<open>Bit operation on \<^typ>\<open>'a word\<close>\<close>

context unique_euclidean_semiring_with_nat
begin

primrec n_bits_of :: "nat \<Rightarrow> 'a \<Rightarrow> bool list"
  where
    "n_bits_of 0 a = []"
  | "n_bits_of (Suc n) a = odd a # n_bits_of n (a div 2)"

lemma n_bits_of_eq_iff:
  "n_bits_of n a = n_bits_of n b \<longleftrightarrow> take_bit n a = take_bit n b"
  apply (induction n arbitrary: a b)
   apply (auto elim!: evenE oddE)
   apply (metis dvd_triv_right even_plus_one_iff)
  apply (metis dvd_triv_right even_plus_one_iff)
  done

lemma take_n_bits_of [simp]:
  "take m (n_bits_of n a) = n_bits_of (min m n) a"
proof -
  define q and v and w where "q = min m n" and "v = m - q" and "w = n - q"
  then have "v = 0 \<or> w = 0"
    by auto
  then have "take (q + v) (n_bits_of (q + w) a) = n_bits_of q a"
    by (induction q arbitrary: a) auto
  with q_def v_def w_def show ?thesis
    by simp
qed

lemma unsigned_of_bits_n_bits_of [simp]:
  "unsigned_of_bits (n_bits_of n a) = take_bit n a"
  by (induction n arbitrary: a) (simp_all add: ac_simps)

end

lemma unsigned_of_bits_eq_of_bits:
  "unsigned_of_bits bs = (of_bits (bs @ [False]) :: int)"
  by (simp add: of_bits_int_def)


instantiation word :: (len) bit_representation
begin

lift_definition bits_of_word :: "'a word \<Rightarrow> bool list"
  is "n_bits_of LENGTH('a)"
  by (simp add: n_bits_of_eq_iff)

lift_definition of_bits_word :: "bool list \<Rightarrow> 'a word"
  is unsigned_of_bits .

instance proof
  fix a :: "'a word"
  show "of_bits (bits_of a) = a"
    by transfer simp
qed

end

lemma take_bit_complement_iff:
  "take_bit n (complement k) = take_bit n (complement l) \<longleftrightarrow> take_bit n k = take_bit n l"
  for k l :: int
  by (simp add: take_bit_eq_mod mod_eq_dvd_iff dvd_diff_commute)

lemma take_bit_not_iff:
  "take_bit n (NOT k) = take_bit n (NOT l) \<longleftrightarrow> take_bit n k = take_bit n l"
  for k l :: int
  by (simp add: not_int_def take_bit_complement_iff)

lemma n_bits_of_not:
  "n_bits_of n (NOT k) = map Not (n_bits_of n k)"
  for k :: int
  by (induction n arbitrary: k) (simp_all add: not_div_2)

lemma take_bit_and [simp]:
  "take_bit n (k AND l) = take_bit n k AND take_bit n l"
  for k l :: int
  apply (induction n arbitrary: k l)
   apply simp
  apply (subst and_int.rec)
  apply (subst (2) and_int.rec)
  apply simp
  done

lemma take_bit_or [simp]:
  "take_bit n (k OR l) = take_bit n k OR take_bit n l"
  for k l :: int
  apply (induction n arbitrary: k l)
   apply simp
  apply (subst or_int.rec)
  apply (subst (2) or_int.rec)
  apply simp
  done

lemma take_bit_xor [simp]:
  "take_bit n (k XOR l) = take_bit n k XOR take_bit n l"
  for k l :: int
  apply (induction n arbitrary: k l)
   apply simp
  apply (subst xor_int.rec)
  apply (subst (2) xor_int.rec)
  apply simp
  done

instantiation word :: (len) bit_operations
begin

lift_definition not_word :: "'a word \<Rightarrow> 'a word"
  is not
  by (simp add: take_bit_not_iff)

lift_definition and_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "and"
  by simp

lift_definition or_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is or
  by simp

lift_definition xor_word ::  "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is xor
  by simp

lift_definition shift_left_word :: "'a word \<Rightarrow> nat \<Rightarrow> 'a word"
  is shift_left
proof -
  show "take_bit LENGTH('a) (k << n) = take_bit LENGTH('a) (l << n)"
    if "take_bit LENGTH('a) k = take_bit LENGTH('a) l" for k l :: int and n :: nat
  proof -
    from that
    have "take_bit (LENGTH('a) - n) (take_bit LENGTH('a) k)
      = take_bit (LENGTH('a) - n) (take_bit LENGTH('a) l)"
      by simp
    moreover have "min (LENGTH('a) - n) LENGTH('a) = LENGTH('a) - n"
      by simp
    ultimately show ?thesis by (simp add: take_bit_push_bit)
  qed
qed

lift_definition shift_right_word :: "'a word \<Rightarrow> nat \<Rightarrow> 'a word"
  is "\<lambda>k n. drop_bit n (take_bit LENGTH('a) k)"
  by simp

instance proof
  show "semilattice ((AND) :: 'a word \<Rightarrow> _)"
    by standard (transfer; simp add: ac_simps)+
  show "semilattice ((OR) :: 'a word \<Rightarrow> _)"
    by standard (transfer; simp add: ac_simps)+
  show "abel_semigroup ((XOR) :: 'a word \<Rightarrow> _)"
    by standard (transfer; simp add: ac_simps)+
  show "not = (of_bits \<circ> map Not \<circ> bits_of :: 'a word \<Rightarrow> 'a word)"
  proof
    fix a :: "'a word"
    have "NOT a = of_bits (map Not (bits_of a))"
      by transfer (simp flip: unsigned_of_bits_take n_bits_of_not add: take_map)
    then show "NOT a = (of_bits \<circ> map Not \<circ> bits_of) a"
      by simp
  qed
  show "of_bits bs AND of_bits cs = (of_bits (map2 (\<and>) bs cs) :: 'a word)"
    if "length bs = length cs" for bs cs
    using that apply transfer
    apply (simp only: unsigned_of_bits_eq_of_bits)
    apply (subst and_eq)
    apply simp_all
    done
  show "of_bits bs OR of_bits cs = (of_bits (map2 (\<or>) bs cs) :: 'a word)"
    if "length bs = length cs" for bs cs
    using that apply transfer
    apply (simp only: unsigned_of_bits_eq_of_bits)
    apply (subst or_eq)
    apply simp_all
    done
  show "of_bits bs XOR of_bits cs = (of_bits (map2 (\<noteq>) bs cs) :: 'a word)"
    if "length bs = length cs" for bs cs
    using that apply transfer
    apply (simp only: unsigned_of_bits_eq_of_bits)
    apply (subst xor_eq)
    apply simp_all
    done
  show "a << n = of_bits (replicate n False @ bits_of a)"
    for a :: "'a word" and n :: nat
    by transfer (simp add: push_bit_take_bit)
  show "a >> n = of_bits (drop n (bits_of a))"
    if "n < length (bits_of a)"
    for a :: "'a word" and n :: nat
    using that by transfer simp
qed


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

end

global_interpretation bit_word: boolean_algebra "(AND)" "(OR)" NOT 0 "- 1 :: 'a::len word"
  rewrites "bit_word.xor = ((XOR) :: 'a word \<Rightarrow> _)"
proof -
  interpret bit_word: boolean_algebra "(AND)" "(OR)" NOT 0 "- 1 :: 'a word"
  proof
    show "a AND (b OR c) = a AND b OR a AND c"
      for a b c :: "'a word"
      by transfer (simp add: bit_int.conj_disj_distrib)
    show "a OR b AND c = (a OR b) AND (a OR c)"
      for a b c :: "'a word"
      by transfer (simp add: bit_int.disj_conj_distrib)
    show "a AND NOT a = 0" for a :: "'a word"
      by transfer simp
    show "a OR NOT a = - 1" for a :: "'a word"
      by transfer simp
  qed (transfer; simp)+
  show "boolean_algebra (AND) (OR) NOT 0 (- 1 :: 'a word)"
    by (fact bit_word.boolean_algebra_axioms)
  show "bit_word.xor = ((XOR) :: 'a word \<Rightarrow> _)"
  proof (rule ext)+
    fix a b :: "'a word"
    have "a XOR b = a AND NOT b OR NOT a AND b"
      by transfer (simp add: bit_int.xor_def)
    then show "bit_word.xor a b = a XOR b"
      by (simp add: bit_word.xor_def)
  qed
qed

end
