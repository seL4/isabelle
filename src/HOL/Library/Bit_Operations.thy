(*  Author:  Florian Haftmann, TUM
*)

section \<open>Bit operations in suitable algebraic structures\<close>

theory Bit_Operations
  imports
    "HOL-Library.Boolean_Algebra"
    Main
begin

subsection \<open>Preliminiaries\<close> \<comment> \<open>TODO move\<close>

lemma take_bit_int_less_exp:
  \<open>take_bit n k < 2 ^ n\<close> for k :: int
  by (simp add: take_bit_eq_mod)

lemma take_bit_Suc_from_most:
  \<open>take_bit (Suc n) k = 2 ^ n * of_bool (bit k n) + take_bit n k\<close> for k :: int
  by (simp only: take_bit_eq_mod power_Suc2) (simp_all add: bit_iff_odd odd_iff_mod_2_eq_one zmod_zmult2_eq)

lemma take_bit_greater_eq:
  \<open>k + 2 ^ n \<le> take_bit n k\<close> if \<open>k < 0\<close> for k :: int
proof -
  have \<open>k + 2 ^ n \<le> take_bit n (k + 2 ^ n)\<close>
  proof (cases \<open>k > - (2 ^ n)\<close>)
    case False
    then have \<open>k + 2 ^ n \<le> 0\<close>
      by simp
    also note take_bit_nonnegative
    finally show ?thesis .
  next
    case True
    with that have \<open>0 \<le> k + 2 ^ n\<close> and \<open>k + 2 ^ n < 2 ^ n\<close>
      by simp_all
    then show ?thesis
      by (simp only: take_bit_eq_mod mod_pos_pos_trivial)
  qed
  then show ?thesis
    by (simp add: take_bit_eq_mod)
qed

lemma take_bit_less_eq:
  \<open>take_bit n k \<le> k - 2 ^ n\<close> if \<open>2 ^ n \<le> k\<close> and \<open>n > 0\<close> for k :: int
  using that zmod_le_nonneg_dividend [of \<open>k - 2 ^ n\<close> \<open>2 ^ n\<close>]
  by (simp add: take_bit_eq_mod)


subsection \<open>Bit operations\<close>

class semiring_bit_operations = semiring_bit_shifts +
  fixes "and" :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>AND\<close> 64)
    and or :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>OR\<close>  59)
    and xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>XOR\<close> 59)
  assumes bit_and_iff: \<open>\<And>n. bit (a AND b) n \<longleftrightarrow> bit a n \<and> bit b n\<close>
    and bit_or_iff: \<open>\<And>n. bit (a OR b) n \<longleftrightarrow> bit a n \<or> bit b n\<close>
    and bit_xor_iff: \<open>\<And>n. bit (a XOR b) n \<longleftrightarrow> bit a n \<noteq> bit b n\<close>
begin

text \<open>
  We want the bitwise operations to bind slightly weaker
  than \<open>+\<close> and \<open>-\<close>.
  For the sake of code generation
  the operations \<^const>\<open>and\<close>, \<^const>\<open>or\<close> and \<^const>\<open>xor\<close>
  are specified as definitional class operations.
\<close>

sublocale "and": semilattice \<open>(AND)\<close>
  by standard (auto simp add: bit_eq_iff bit_and_iff)

sublocale or: semilattice_neutr \<open>(OR)\<close> 0
  by standard (auto simp add: bit_eq_iff bit_or_iff)

sublocale xor: comm_monoid \<open>(XOR)\<close> 0
  by standard (auto simp add: bit_eq_iff bit_xor_iff)

lemma even_and_iff:
  \<open>even (a AND b) \<longleftrightarrow> even a \<or> even b\<close>
  using bit_and_iff [of a b 0] by auto

lemma even_or_iff:
  \<open>even (a OR b) \<longleftrightarrow> even a \<and> even b\<close>
  using bit_or_iff [of a b 0] by auto

lemma even_xor_iff:
  \<open>even (a XOR b) \<longleftrightarrow> (even a \<longleftrightarrow> even b)\<close>
  using bit_xor_iff [of a b 0] by auto

lemma zero_and_eq [simp]:
  "0 AND a = 0"
  by (simp add: bit_eq_iff bit_and_iff)

lemma and_zero_eq [simp]:
  "a AND 0 = 0"
  by (simp add: bit_eq_iff bit_and_iff)

lemma one_and_eq:
  "1 AND a = a mod 2"
  by (simp add: bit_eq_iff bit_and_iff) (auto simp add: bit_1_iff)

lemma and_one_eq:
  "a AND 1 = a mod 2"
  using one_and_eq [of a] by (simp add: ac_simps)

lemma one_or_eq:
  "1 OR a = a + of_bool (even a)"
  by (simp add: bit_eq_iff bit_or_iff add.commute [of _ 1] even_bit_succ_iff) (auto simp add: bit_1_iff)

lemma or_one_eq:
  "a OR 1 = a + of_bool (even a)"
  using one_or_eq [of a] by (simp add: ac_simps)

lemma one_xor_eq:
  "1 XOR a = a + of_bool (even a) - of_bool (odd a)"
  by (simp add: bit_eq_iff bit_xor_iff add.commute [of _ 1] even_bit_succ_iff) (auto simp add: bit_1_iff odd_bit_iff_bit_pred elim: oddE)

lemma xor_one_eq:
  "a XOR 1 = a + of_bool (even a) - of_bool (odd a)"
  using one_xor_eq [of a] by (simp add: ac_simps)

lemma take_bit_and [simp]:
  \<open>take_bit n (a AND b) = take_bit n a AND take_bit n b\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_and_iff)

lemma take_bit_or [simp]:
  \<open>take_bit n (a OR b) = take_bit n a OR take_bit n b\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_or_iff)

lemma take_bit_xor [simp]:
  \<open>take_bit n (a XOR b) = take_bit n a XOR take_bit n b\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_xor_iff)

definition mask :: \<open>nat \<Rightarrow> 'a\<close>
  where mask_eq_exp_minus_1: \<open>mask n = 2 ^ n - 1\<close>

lemma bit_mask_iff:
  \<open>bit (mask m) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n < m\<close>
  by (simp add: mask_eq_exp_minus_1 bit_mask_iff)

lemma even_mask_iff:
  \<open>even (mask n) \<longleftrightarrow> n = 0\<close>
  using bit_mask_iff [of n 0] by auto

lemma mask_0 [simp, code]:
  \<open>mask 0 = 0\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma mask_Suc_exp [code]:
  \<open>mask (Suc n) = 2 ^ n OR mask n\<close>
  by (rule bit_eqI)
    (auto simp add: bit_or_iff bit_mask_iff bit_exp_iff not_less le_less_Suc_eq)

lemma mask_Suc_double:
  \<open>mask (Suc n) = 2 * mask n OR 1\<close>
proof (rule bit_eqI)
  fix q
  assume \<open>2 ^ q \<noteq> 0\<close>
  show \<open>bit (mask (Suc n)) q \<longleftrightarrow> bit (2 * mask n OR 1) q\<close>
    by (cases q)
      (simp_all add: even_mask_iff even_or_iff bit_or_iff bit_mask_iff bit_exp_iff bit_double_iff not_less le_less_Suc_eq bit_1_iff, auto simp add: mult_2)
qed

lemma take_bit_eq_mask:
  \<open>take_bit n a = a AND mask n\<close>
  by (rule bit_eqI)
    (auto simp add: bit_take_bit_iff bit_and_iff bit_mask_iff)

end

class ring_bit_operations = semiring_bit_operations + ring_parity +
  fixes not :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>NOT\<close>)
  assumes bit_not_iff: \<open>\<And>n. bit (NOT a) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> \<not> bit a n\<close>
  assumes minus_eq_not_minus_1: \<open>- a = NOT (a - 1)\<close>
begin

text \<open>
  For the sake of code generation \<^const>\<open>not\<close> is specified as
  definitional class operation.  Note that \<^const>\<open>not\<close> has no
  sensible definition for unlimited but only positive bit strings
  (type \<^typ>\<open>nat\<close>).
\<close>

lemma bits_minus_1_mod_2_eq [simp]:
  \<open>(- 1) mod 2 = 1\<close>
  by (simp add: mod_2_eq_odd)

lemma not_eq_complement:
  \<open>NOT a = - a - 1\<close>
  using minus_eq_not_minus_1 [of \<open>a + 1\<close>] by simp

lemma minus_eq_not_plus_1:
  \<open>- a = NOT a + 1\<close>
  using not_eq_complement [of a] by simp

lemma bit_minus_iff:
  \<open>bit (- a) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> \<not> bit (a - 1) n\<close>
  by (simp add: minus_eq_not_minus_1 bit_not_iff)

lemma even_not_iff [simp]:
  "even (NOT a) \<longleftrightarrow> odd a"
  using bit_not_iff [of a 0] by auto

lemma bit_not_exp_iff:
  \<open>bit (NOT (2 ^ m)) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n \<noteq> m\<close>
  by (auto simp add: bit_not_iff bit_exp_iff)

lemma bit_minus_1_iff [simp]:
  \<open>bit (- 1) n \<longleftrightarrow> 2 ^ n \<noteq> 0\<close>
  by (simp add: bit_minus_iff)

lemma bit_minus_exp_iff:
  \<open>bit (- (2 ^ m)) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n \<ge> m\<close>
  oops

lemma bit_minus_2_iff [simp]:
  \<open>bit (- 2) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n > 0\<close>
  by (simp add: bit_minus_iff bit_1_iff)

lemma not_one [simp]:
  "NOT 1 = - 2"
  by (simp add: bit_eq_iff bit_not_iff) (simp add: bit_1_iff)

sublocale "and": semilattice_neutr \<open>(AND)\<close> \<open>- 1\<close>
  apply standard
  apply (simp add: bit_eq_iff bit_and_iff)
  apply (auto simp add: exp_eq_0_imp_not_bit bit_exp_iff)
  done

sublocale bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
  rewrites \<open>bit.xor = (XOR)\<close>
proof -
  interpret bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
    apply standard
         apply (simp_all add: bit_eq_iff)
       apply (auto simp add: bit_and_iff bit_or_iff bit_not_iff bit_exp_iff exp_eq_0_imp_not_bit)
    done
  show \<open>boolean_algebra (AND) (OR) NOT 0 (- 1)\<close>
    by standard
  show \<open>boolean_algebra.xor (AND) (OR) NOT = (XOR)\<close>
    apply (simp add: fun_eq_iff bit_eq_iff bit.xor_def)
    apply (auto simp add: bit_and_iff bit_or_iff bit_not_iff bit_xor_iff exp_eq_0_imp_not_bit)
    done
qed

lemma and_eq_not_not_or:
  \<open>a AND b = NOT (NOT a OR NOT b)\<close>
  by simp

lemma or_eq_not_not_and:
  \<open>a OR b = NOT (NOT a AND NOT b)\<close>
  by simp

lemma not_add_distrib:
  \<open>NOT (a + b) = NOT a - b\<close>
  by (simp add: not_eq_complement algebra_simps)

lemma not_diff_distrib:
  \<open>NOT (a - b) = NOT a + b\<close>
  using not_add_distrib [of a \<open>- b\<close>] by simp

lemma push_bit_minus:
  \<open>push_bit n (- a) = - push_bit n a\<close>
  by (simp add: push_bit_eq_mult)

lemma take_bit_not_take_bit:
  \<open>take_bit n (NOT (take_bit n a)) = take_bit n (NOT a)\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_not_iff)

lemma take_bit_not_iff:
  "take_bit n (NOT a) = take_bit n (NOT b) \<longleftrightarrow> take_bit n a = take_bit n b"
  apply (simp add: bit_eq_iff bit_not_iff bit_take_bit_iff)
  apply (simp add: bit_exp_iff)
  apply (use local.exp_eq_0_imp_not_bit in blast)
  done

lemma take_bit_minus_one_eq_mask:
  \<open>take_bit n (- 1) = mask n\<close>
  by (simp add: bit_eq_iff bit_mask_iff bit_take_bit_iff conj_commute)

lemma minus_exp_eq_not_mask:
  \<open>- (2 ^ n) = NOT (mask n)\<close>
  by (rule bit_eqI) (simp add: bit_minus_iff bit_not_iff flip: mask_eq_exp_minus_1)

lemma push_bit_minus_one_eq_not_mask:
  \<open>push_bit n (- 1) = NOT (mask n)\<close>
  by (simp add: push_bit_eq_mult minus_exp_eq_not_mask)

lemma take_bit_not_mask_eq_0:
  \<open>take_bit m (NOT (mask n)) = 0\<close> if \<open>n \<ge> m\<close>
  by (rule bit_eqI) (use that in \<open>simp add: bit_take_bit_iff bit_not_iff bit_mask_iff\<close>)

definition set_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>set_bit n a = a OR push_bit n 1\<close>

definition unset_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>unset_bit n a = a AND NOT (push_bit n 1)\<close>

definition flip_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>flip_bit n a = a XOR push_bit n 1\<close>

lemma bit_set_bit_iff:
  \<open>bit (set_bit m a) n \<longleftrightarrow> bit a n \<or> (m = n \<and> 2 ^ n \<noteq> 0)\<close>
  by (auto simp add: set_bit_def push_bit_of_1 bit_or_iff bit_exp_iff)

lemma even_set_bit_iff:
  \<open>even (set_bit m a) \<longleftrightarrow> even a \<and> m \<noteq> 0\<close>
  using bit_set_bit_iff [of m a 0] by auto

lemma bit_unset_bit_iff:
  \<open>bit (unset_bit m a) n \<longleftrightarrow> bit a n \<and> m \<noteq> n\<close>
  by (auto simp add: unset_bit_def push_bit_of_1 bit_and_iff bit_not_iff bit_exp_iff exp_eq_0_imp_not_bit)

lemma even_unset_bit_iff:
  \<open>even (unset_bit m a) \<longleftrightarrow> even a \<or> m = 0\<close>
  using bit_unset_bit_iff [of m a 0] by auto

lemma bit_flip_bit_iff:
  \<open>bit (flip_bit m a) n \<longleftrightarrow> (m = n \<longleftrightarrow> \<not> bit a n) \<and> 2 ^ n \<noteq> 0\<close>
  by (auto simp add: flip_bit_def push_bit_of_1 bit_xor_iff bit_exp_iff exp_eq_0_imp_not_bit)

lemma even_flip_bit_iff:
  \<open>even (flip_bit m a) \<longleftrightarrow> \<not> (even a \<longleftrightarrow> m = 0)\<close>
  using bit_flip_bit_iff [of m a 0] by auto

lemma set_bit_0 [simp]:
  \<open>set_bit 0 a = 1 + 2 * (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (set_bit 0 a) m = bit (1 + 2 * (a div 2)) m\<close>
    by (simp add: bit_set_bit_iff bit_double_iff even_bit_succ_iff)
      (cases m, simp_all add: bit_Suc)
qed

lemma set_bit_Suc:
  \<open>set_bit (Suc n) a = a mod 2 + 2 * set_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  show \<open>bit (set_bit (Suc n) a) m \<longleftrightarrow> bit (a mod 2 + 2 * set_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_set_bit_iff)
  next
    case (Suc m)
    with * have \<open>2 ^ m \<noteq> 0\<close>
      using mult_2 by auto
    show ?thesis
      by (cases a rule: parity_cases)
        (simp_all add: bit_set_bit_iff bit_double_iff even_bit_succ_iff *,
        simp_all add: Suc \<open>2 ^ m \<noteq> 0\<close> bit_Suc)
  qed
qed

lemma unset_bit_0 [simp]:
  \<open>unset_bit 0 a = 2 * (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (unset_bit 0 a) m = bit (2 * (a div 2)) m\<close>
    by (simp add: bit_unset_bit_iff bit_double_iff)
      (cases m, simp_all add: bit_Suc)
qed

lemma unset_bit_Suc:
  \<open>unset_bit (Suc n) a = a mod 2 + 2 * unset_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (unset_bit (Suc n) a) m \<longleftrightarrow> bit (a mod 2 + 2 * unset_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_unset_bit_iff)
  next
    case (Suc m)
    show ?thesis
      by (cases a rule: parity_cases)
        (simp_all add: bit_unset_bit_iff bit_double_iff even_bit_succ_iff *,
         simp_all add: Suc bit_Suc)
  qed
qed

lemma flip_bit_0 [simp]:
  \<open>flip_bit 0 a = of_bool (even a) + 2 * (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (flip_bit 0 a) m = bit (of_bool (even a) + 2 * (a div 2)) m\<close>
    by (simp add: bit_flip_bit_iff bit_double_iff even_bit_succ_iff)
      (cases m, simp_all add: bit_Suc)
qed

lemma flip_bit_Suc:
  \<open>flip_bit (Suc n) a = a mod 2 + 2 * flip_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  show \<open>bit (flip_bit (Suc n) a) m \<longleftrightarrow> bit (a mod 2 + 2 * flip_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_flip_bit_iff)
  next
    case (Suc m)
    with * have \<open>2 ^ m \<noteq> 0\<close>
      using mult_2 by auto
    show ?thesis
      by (cases a rule: parity_cases)
        (simp_all add: bit_flip_bit_iff bit_double_iff even_bit_succ_iff,
        simp_all add: Suc \<open>2 ^ m \<noteq> 0\<close> bit_Suc)
  qed
qed

lemma flip_bit_eq_if:
  \<open>flip_bit n a = (if bit a n then unset_bit else set_bit) n a\<close>
  by (rule bit_eqI) (auto simp add: bit_set_bit_iff bit_unset_bit_iff bit_flip_bit_iff)

lemma take_bit_set_bit_eq:
  \<open>take_bit n (set_bit m a) = (if n \<le> m then take_bit n a else set_bit m (take_bit n a))\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_set_bit_iff)

lemma take_bit_unset_bit_eq:
  \<open>take_bit n (unset_bit m a) = (if n \<le> m then take_bit n a else unset_bit m (take_bit n a))\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_unset_bit_iff)

lemma take_bit_flip_bit_eq:
  \<open>take_bit n (flip_bit m a) = (if n \<le> m then take_bit n a else flip_bit m (take_bit n a))\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_flip_bit_iff)

end


subsection \<open>Instance \<^typ>\<open>int\<close>\<close>

instantiation int :: ring_bit_operations
begin

definition not_int :: \<open>int \<Rightarrow> int\<close>
  where \<open>not_int k = - k - 1\<close>

lemma not_int_rec:
  "NOT k = of_bool (even k) + 2 * NOT (k div 2)" for k :: int
  by (auto simp add: not_int_def elim: oddE)

lemma even_not_iff_int:
  \<open>even (NOT k) \<longleftrightarrow> odd k\<close> for k :: int
  by (simp add: not_int_def)

lemma not_int_div_2:
  \<open>NOT k div 2 = NOT (k div 2)\<close> for k :: int
  by (simp add: not_int_def)

lemma bit_not_int_iff:
  \<open>bit (NOT k) n \<longleftrightarrow> \<not> bit k n\<close>
    for k :: int
  by (induction n arbitrary: k) (simp_all add: not_int_div_2 even_not_iff_int bit_Suc)

function and_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>(k::int) AND l = (if k \<in> {0, - 1} \<and> l \<in> {0, - 1}
    then - of_bool (odd k \<and> odd l)
    else of_bool (odd k \<and> odd l) + 2 * ((k div 2) AND (l div 2)))\<close>
  by auto

termination
  by (relation \<open>measure (\<lambda>(k, l). nat (\<bar>k\<bar> + \<bar>l\<bar>))\<close>) auto

declare and_int.simps [simp del]

lemma and_int_rec:
  \<open>k AND l = of_bool (odd k \<and> odd l) + 2 * ((k div 2) AND (l div 2))\<close>
    for k l :: int
proof (cases \<open>k \<in> {0, - 1} \<and> l \<in> {0, - 1}\<close>)
  case True
  then show ?thesis
    by auto (simp_all add: and_int.simps)
next
  case False
  then show ?thesis
    by (auto simp add: ac_simps and_int.simps [of k l])
qed

lemma bit_and_int_iff:
  \<open>bit (k AND l) n \<longleftrightarrow> bit k n \<and> bit l n\<close> for k l :: int
proof (induction n arbitrary: k l)
  case 0
  then show ?case
    by (simp add: and_int_rec [of k l])
next
  case (Suc n)
  then show ?case
    by (simp add: and_int_rec [of k l] bit_Suc)
qed

lemma even_and_iff_int:
  \<open>even (k AND l) \<longleftrightarrow> even k \<or> even l\<close> for k l :: int
  using bit_and_int_iff [of k l 0] by auto

definition or_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k OR l = NOT (NOT k AND NOT l)\<close> for k l :: int

lemma or_int_rec:
  \<open>k OR l = of_bool (odd k \<or> odd l) + 2 * ((k div 2) OR (l div 2))\<close>
  for k l :: int
  using and_int_rec [of \<open>NOT k\<close> \<open>NOT l\<close>]
  by (simp add: or_int_def even_not_iff_int not_int_div_2)
    (simp add: not_int_def)

lemma bit_or_int_iff:
  \<open>bit (k OR l) n \<longleftrightarrow> bit k n \<or> bit l n\<close> for k l :: int
  by (simp add: or_int_def bit_not_int_iff bit_and_int_iff)

definition xor_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k XOR l = k AND NOT l OR NOT k AND l\<close> for k l :: int

lemma xor_int_rec:
  \<open>k XOR l = of_bool (odd k \<noteq> odd l) + 2 * ((k div 2) XOR (l div 2))\<close>
  for k l :: int
  by (simp add: xor_int_def or_int_rec [of \<open>k AND NOT l\<close> \<open>NOT k AND l\<close>] even_and_iff_int even_not_iff_int)
    (simp add: and_int_rec [of \<open>NOT k\<close> \<open>l\<close>] and_int_rec [of \<open>k\<close> \<open>NOT l\<close>] not_int_div_2)

lemma bit_xor_int_iff:
  \<open>bit (k XOR l) n \<longleftrightarrow> bit k n \<noteq> bit l n\<close> for k l :: int
  by (auto simp add: xor_int_def bit_or_int_iff bit_and_int_iff bit_not_int_iff)

instance proof
  fix k l :: int and n :: nat
  show \<open>- k = NOT (k - 1)\<close>
    by (simp add: not_int_def)
  show \<open>bit (k AND l) n \<longleftrightarrow> bit k n \<and> bit l n\<close>
    by (fact bit_and_int_iff)
  show \<open>bit (k OR l) n \<longleftrightarrow> bit k n \<or> bit l n\<close>
    by (fact bit_or_int_iff)
  show \<open>bit (k XOR l) n \<longleftrightarrow> bit k n \<noteq> bit l n\<close>
    by (fact bit_xor_int_iff)
qed (simp_all add: bit_not_int_iff)

end

lemma disjunctive_add:
  \<open>k + l = k OR l\<close> if \<open>\<And>n. \<not> bit k n \<or> \<not> bit l n\<close> for k l :: int
  \<comment> \<open>TODO: may integrate (indirectly) into \<^class>\<open>semiring_bits\<close> premises\<close>
proof (rule bit_eqI)
  fix n
  from that have \<open>bit (k + l) n \<longleftrightarrow> bit k n \<or> bit l n\<close>
  proof (induction n arbitrary: k l)
    case 0
    from this [of 0] show ?case
      by auto
  next
    case (Suc n)
    have \<open>bit ((k + l) div 2) n \<longleftrightarrow> bit (k div 2 + l div 2) n\<close>
      using Suc.prems [of 0] div_add1_eq [of k l] by auto
    also have \<open>bit (k div 2 + l div 2) n \<longleftrightarrow> bit (k div 2) n \<or> bit (l div 2) n\<close>
      by (rule Suc.IH) (use Suc.prems in \<open>simp flip: bit_Suc\<close>)
    finally show ?case
      by (simp add: bit_Suc)
  qed
  also have \<open>\<dots> \<longleftrightarrow> bit (k OR l) n\<close>
    by (simp add: bit_or_iff)
  finally show \<open>bit (k + l) n \<longleftrightarrow> bit (k OR l) n\<close> .
qed

lemma disjunctive_diff:
  \<open>k - l = k AND NOT l\<close> if \<open>\<And>n. bit l n \<Longrightarrow> bit k n\<close> for k l :: int
proof -
  have \<open>NOT k + l = NOT k OR l\<close>
    by (rule disjunctive_add) (auto simp add: bit_not_iff dest: that)
  then have \<open>NOT (NOT k + l) = NOT (NOT k OR l)\<close>
    by simp
  then show ?thesis
    by (simp add: not_add_distrib)
qed

lemma not_nonnegative_int_iff [simp]:
  \<open>NOT k \<ge> 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: not_int_def)

lemma not_negative_int_iff [simp]:
  \<open>NOT k < 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (subst Not_eq_iff [symmetric]) (simp add: not_less not_le)

lemma and_nonnegative_int_iff [simp]:
  \<open>k AND l \<ge> 0 \<longleftrightarrow> k \<ge> 0 \<or> l \<ge> 0\<close> for k l :: int
proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even k)
  then show ?case
    using and_int_rec [of \<open>k * 2\<close> l] by (simp add: pos_imp_zdiv_nonneg_iff)
next
  case (odd k)
  from odd have \<open>0 \<le> k AND l div 2 \<longleftrightarrow> 0 \<le> k \<or> 0 \<le> l div 2\<close>
    by simp
  then have \<open>0 \<le> (1 + k * 2) div 2 AND l div 2 \<longleftrightarrow> 0 \<le> (1 + k * 2) div 2\<or> 0 \<le> l div 2\<close>
    by simp
  with and_int_rec [of \<open>1 + k * 2\<close> l]
  show ?case
    by auto
qed

lemma and_negative_int_iff [simp]:
  \<open>k AND l < 0 \<longleftrightarrow> k < 0 \<and> l < 0\<close> for k l :: int
  by (subst Not_eq_iff [symmetric]) (simp add: not_less)

lemma and_less_eq:
  \<open>k AND l \<le> k\<close> if \<open>l < 0\<close> for k l :: int
using that proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even k)
  from even.IH [of \<open>l div 2\<close>] even.hyps even.prems
  show ?case
    by (simp add: and_int_rec [of _ l])
next
  case (odd k)
  from odd.IH [of \<open>l div 2\<close>] odd.hyps odd.prems
  show ?case
    by (simp add: and_int_rec [of _ l])
qed

lemma or_nonnegative_int_iff [simp]:
  \<open>k OR l \<ge> 0 \<longleftrightarrow> k \<ge> 0 \<and> l \<ge> 0\<close> for k l :: int
  by (simp only: or_eq_not_not_and not_nonnegative_int_iff) simp

lemma or_negative_int_iff [simp]:
  \<open>k OR l < 0 \<longleftrightarrow> k < 0 \<or> l < 0\<close> for k l :: int
  by (subst Not_eq_iff [symmetric]) (simp add: not_less)

lemma or_greater_eq:
  \<open>k OR l \<ge> k\<close> if \<open>l \<ge> 0\<close> for k l :: int
using that proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even k)
  from even.IH [of \<open>l div 2\<close>] even.hyps even.prems
  show ?case
    by (simp add: or_int_rec [of _ l])
next
  case (odd k)
  from odd.IH [of \<open>l div 2\<close>] odd.hyps odd.prems
  show ?case
    by (simp add: or_int_rec [of _ l])
qed

lemma xor_nonnegative_int_iff [simp]:
  \<open>k XOR l \<ge> 0 \<longleftrightarrow> (k \<ge> 0 \<longleftrightarrow> l \<ge> 0)\<close> for k l :: int
  by (simp only: bit.xor_def or_nonnegative_int_iff) auto

lemma xor_negative_int_iff [simp]:
  \<open>k XOR l < 0 \<longleftrightarrow> (k < 0) \<noteq> (l < 0)\<close> for k l :: int
  by (subst Not_eq_iff [symmetric]) (auto simp add: not_less)

lemma mask_nonnegative:
  \<open>(mask n :: int) \<ge> 0\<close>
 by (simp add: mask_eq_exp_minus_1)  

lemma set_bit_nonnegative_int_iff [simp]:
  \<open>set_bit n k \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (simp add: set_bit_def)

lemma set_bit_negative_int_iff [simp]:
  \<open>set_bit n k < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: set_bit_def)

lemma unset_bit_nonnegative_int_iff [simp]:
  \<open>unset_bit n k \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (simp add: unset_bit_def)

lemma unset_bit_negative_int_iff [simp]:
  \<open>unset_bit n k < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: unset_bit_def)

lemma flip_bit_nonnegative_int_iff [simp]:
  \<open>flip_bit n k \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (simp add: flip_bit_def)

lemma flip_bit_negative_int_iff [simp]:
  \<open>flip_bit n k < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: flip_bit_def)

lemma set_bit_greater_eq:
  \<open>set_bit n k \<ge> k\<close> for k :: int
  by (simp add: set_bit_def or_greater_eq)

lemma unset_bit_less_eq:
  \<open>unset_bit n k \<le> k\<close> for k :: int
  by (simp add: unset_bit_def and_less_eq)

lemma set_bit_eq:
  \<open>set_bit n k = k + of_bool (\<not> bit k n) * 2 ^ n\<close> for k :: int
proof (rule bit_eqI)
  fix m
  show \<open>bit (set_bit n k) m \<longleftrightarrow> bit (k + of_bool (\<not> bit k n) * 2 ^ n) m\<close>
  proof (cases \<open>m = n\<close>)
    case True
    then show ?thesis
      apply (simp add: bit_set_bit_iff)
      apply (simp add: bit_iff_odd div_plus_div_distrib_dvd_right)
      done
  next
    case False
    then show ?thesis
      apply (clarsimp simp add: bit_set_bit_iff)
      apply (subst disjunctive_add)
      apply (clarsimp simp add: bit_exp_iff)
      apply (clarsimp simp add: bit_or_iff bit_exp_iff)
      done
  qed
qed

lemma unset_bit_eq:
  \<open>unset_bit n k = k - of_bool (bit k n) * 2 ^ n\<close> for k :: int
proof (rule bit_eqI)
  fix m
  show \<open>bit (unset_bit n k) m \<longleftrightarrow> bit (k - of_bool (bit k n) * 2 ^ n) m\<close>
  proof (cases \<open>m = n\<close>)
    case True
    then show ?thesis
      apply (simp add: bit_unset_bit_iff)
      apply (simp add: bit_iff_odd)
      using div_plus_div_distrib_dvd_right [of \<open>2 ^ n\<close> \<open>- (2 ^ n)\<close> k]
      apply (simp add: dvd_neg_div)
      done
  next
    case False
    then show ?thesis
      apply (clarsimp simp add: bit_unset_bit_iff)
      apply (subst disjunctive_diff)
      apply (clarsimp simp add: bit_exp_iff)
      apply (clarsimp simp add: bit_and_iff bit_not_iff bit_exp_iff)
      done
  qed
qed


subsection \<open>Taking bit with sign propagation\<close>

definition signed_take_bit :: "nat \<Rightarrow> int \<Rightarrow> int"
  where \<open>signed_take_bit n k = take_bit n k OR (NOT (mask n) * of_bool (bit k n))\<close>

lemma signed_take_bit_eq:
  \<open>signed_take_bit n k = take_bit n k\<close> if \<open>\<not> bit k n\<close>
  using that by (simp add: signed_take_bit_def)

lemma signed_take_bit_eq_or:
  \<open>signed_take_bit n k = take_bit n k OR NOT (mask n)\<close> if \<open>bit k n\<close>
  using that by (simp add: signed_take_bit_def)

lemma signed_take_bit_0 [simp]:
  \<open>signed_take_bit 0 k = - (k mod 2)\<close>
  by (simp add: signed_take_bit_def odd_iff_mod_2_eq_one)

lemma mask_half_int:
  \<open>mask n div 2 = (mask (n - 1) :: int)\<close>
  by (cases n) (simp_all add: mask_eq_exp_minus_1 algebra_simps)

lemma signed_take_bit_Suc:
  \<open>signed_take_bit (Suc n) k = k mod 2 + 2 * signed_take_bit n (k div 2)\<close>
  by (unfold signed_take_bit_def or_int_rec [of \<open>take_bit (Suc n) k\<close>])
    (simp add: bit_Suc take_bit_Suc even_or_iff even_mask_iff odd_iff_mod_2_eq_one not_int_div_2 mask_half_int)

lemma signed_take_bit_rec:
  \<open>signed_take_bit n k = (if n = 0 then - (k mod 2) else k mod 2 + 2 * signed_take_bit (n - 1) (k div 2))\<close>
  by (cases n) (simp_all add: signed_take_bit_Suc)

lemma bit_signed_take_bit_iff:
  \<open>bit (signed_take_bit m k) n = bit k (min m n)\<close>
  by (simp add: signed_take_bit_def bit_or_iff bit_take_bit_iff bit_not_iff bit_mask_iff min_def)

text \<open>Modulus centered around 0\<close>

lemma signed_take_bit_eq_take_bit_minus:
  \<open>signed_take_bit n k = take_bit (Suc n) k - 2 ^ Suc n * of_bool (bit k n)\<close>
proof (cases \<open>bit k n\<close>)
  case True
  have \<open>signed_take_bit n k = take_bit (Suc n) k OR NOT (mask (Suc n))\<close>
    by (rule bit_eqI) (auto simp add: bit_signed_take_bit_iff min_def bit_take_bit_iff bit_or_iff bit_not_iff bit_mask_iff less_Suc_eq True)
  then have \<open>signed_take_bit n k = take_bit (Suc n) k + NOT (mask (Suc n))\<close>
    by (simp add: disjunctive_add bit_take_bit_iff bit_not_iff bit_mask_iff)
  with True show ?thesis
    by (simp flip: minus_exp_eq_not_mask)
next
  case False
  then show ?thesis
    by (simp add: bit_eq_iff bit_take_bit_iff bit_signed_take_bit_iff min_def)
      (auto intro: bit_eqI simp add: less_Suc_eq)
qed

lemma signed_take_bit_eq_take_bit_shift:
  \<open>signed_take_bit n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n\<close>
proof -
  have *: \<open>take_bit n k OR 2 ^ n = take_bit n k + 2 ^ n\<close>
    by (simp add: disjunctive_add bit_exp_iff bit_take_bit_iff)
  have \<open>take_bit n k - 2 ^ n = take_bit n k + NOT (mask n)\<close>
    by (simp add: minus_exp_eq_not_mask)
  also have \<open>\<dots> = take_bit n k OR NOT (mask n)\<close>
    by (rule disjunctive_add)
      (simp add: bit_exp_iff bit_take_bit_iff bit_not_iff bit_mask_iff)
  finally have **: \<open>take_bit n k - 2 ^ n = take_bit n k OR NOT (mask n)\<close> .
  have \<open>take_bit (Suc n) (k + 2 ^ n) = take_bit (Suc n) (take_bit (Suc n) k + take_bit (Suc n) (2 ^ n))\<close>
    by (simp only: take_bit_add)
  also have \<open>take_bit (Suc n) k = 2 ^ n * of_bool (bit k n) + take_bit n k\<close>
    by (simp add: take_bit_Suc_from_most)
  finally have \<open>take_bit (Suc n) (k + 2 ^ n) = take_bit (Suc n) (2 ^ (n + of_bool (bit k n)) + take_bit n k)\<close>
    by (simp add: ac_simps)
  also have \<open>2 ^ (n + of_bool (bit k n)) + take_bit n k = 2 ^ (n + of_bool (bit k n)) OR take_bit n k\<close>
    by (rule disjunctive_add)
      (auto simp add: disjunctive_add bit_take_bit_iff bit_double_iff bit_exp_iff)
  finally show ?thesis
    using * ** by (simp add: signed_take_bit_def take_bit_Suc min_def ac_simps)
qed

lemma signed_take_bit_of_0 [simp]:
  \<open>signed_take_bit n 0 = 0\<close>
  by (simp add: signed_take_bit_def)

lemma signed_take_bit_of_minus_1 [simp]:
  \<open>signed_take_bit n (- 1) = - 1\<close>
  by (simp add: signed_take_bit_def take_bit_minus_one_eq_mask)

lemma signed_take_bit_eq_iff_take_bit_eq:
  \<open>signed_take_bit n k = signed_take_bit n l \<longleftrightarrow> take_bit (Suc n) k = take_bit (Suc n) l\<close>
proof (cases \<open>bit k n \<longleftrightarrow> bit l n\<close>)
  case True
  moreover have \<open>take_bit n k OR NOT (mask n) = take_bit n k - 2 ^ n\<close>
    for k :: int
    by (auto simp add: disjunctive_add [symmetric] bit_not_iff bit_mask_iff bit_take_bit_iff minus_exp_eq_not_mask)
  ultimately show ?thesis
    by (simp add: signed_take_bit_def take_bit_Suc_from_most)
next
  case False
  then have \<open>signed_take_bit n k \<noteq> signed_take_bit n l\<close> and \<open>take_bit (Suc n) k \<noteq> take_bit (Suc n) l\<close>
    by (auto simp add: bit_eq_iff bit_take_bit_iff bit_signed_take_bit_iff min_def)
  then show ?thesis
    by simp
qed

lemma signed_take_bit_signed_take_bit [simp]:
  \<open>signed_take_bit m (signed_take_bit n k) = signed_take_bit (min m n) k\<close>
  by (rule bit_eqI) (auto simp add: bit_signed_take_bit_iff min_def bit_or_iff bit_not_iff bit_mask_iff bit_take_bit_iff)

lemma take_bit_signed_take_bit:
  \<open>take_bit m (signed_take_bit n k) = take_bit m k\<close> if \<open>m \<le> n\<close>
  using that by (auto simp add: bit_eq_iff bit_take_bit_iff bit_signed_take_bit_iff min_def)

lemma take_bit_Suc_signed_take_bit [simp]:
  \<open>take_bit (Suc n) (signed_take_bit n a) = take_bit (Suc n) a\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_signed_take_bit_iff min_def less_Suc_eq)

lemma signed_take_bit_take_bit:
  \<open>signed_take_bit m (take_bit n k) = (if n \<le> m then take_bit n else signed_take_bit m) k\<close>
  by (rule bit_eqI) (auto simp add: bit_signed_take_bit_iff min_def bit_take_bit_iff)

lemma signed_take_bit_nonnegative_iff [simp]:
  \<open>0 \<le> signed_take_bit n k \<longleftrightarrow> \<not> bit k n\<close>
  by (simp add: signed_take_bit_def not_less mask_nonnegative)

lemma signed_take_bit_negative_iff [simp]:
  \<open>signed_take_bit n k < 0 \<longleftrightarrow> bit k n\<close>
  by (simp add: signed_take_bit_def not_less mask_nonnegative)

lemma signed_take_bit_greater_eq:
  \<open>k + 2 ^ Suc n \<le> signed_take_bit n k\<close> if \<open>k < - (2 ^ n)\<close>
  using that take_bit_greater_eq [of \<open>k + 2 ^ n\<close> \<open>Suc n\<close>]
  by (simp add: signed_take_bit_eq_take_bit_shift)

lemma signed_take_bit_less_eq:
  \<open>signed_take_bit n k \<le> k - 2 ^ Suc n\<close> if \<open>k \<ge> 2 ^ n\<close>
  using that take_bit_less_eq [of \<open>Suc n\<close> \<open>k + 2 ^ n\<close>]
  by (simp add: signed_take_bit_eq_take_bit_shift)

lemma signed_take_bit_Suc_1 [simp]:
  \<open>signed_take_bit (Suc n) 1 = 1\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_bit0 [simp]:
  \<open>signed_take_bit (Suc n) (numeral (Num.Bit0 k)) = signed_take_bit n (numeral k) * 2\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_bit1 [simp]:
  \<open>signed_take_bit (Suc n) (numeral (Num.Bit1 k)) = signed_take_bit n (numeral k) * 2 + 1\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_minus_bit0 [simp]:
  \<open>signed_take_bit (Suc n) (- numeral (Num.Bit0 k)) = signed_take_bit n (- numeral k) * 2\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_minus_bit1 [simp]:
  \<open>signed_take_bit (Suc n) (- numeral (Num.Bit1 k)) = signed_take_bit n (- numeral k - 1) * 2 + 1\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_numeral_bit0 [simp]:
  \<open>signed_take_bit (numeral l) (numeral (Num.Bit0 k)) = signed_take_bit (pred_numeral l) (numeral k) * 2\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_numeral_bit1 [simp]:
  \<open>signed_take_bit (numeral l) (numeral (Num.Bit1 k)) = signed_take_bit (pred_numeral l) (numeral k) * 2 + 1\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_numeral_minus_bit0 [simp]:
  \<open>signed_take_bit (numeral l) (- numeral (Num.Bit0 k)) = signed_take_bit (pred_numeral l) (- numeral k) * 2\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_numeral_minus_bit1 [simp]:
  \<open>signed_take_bit (numeral l) (- numeral (Num.Bit1 k)) = signed_take_bit (pred_numeral l) (- numeral k - 1) * 2 + 1\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_code [code]:
  \<open>signed_take_bit n k =
  (let l = k AND mask (Suc n)
   in if bit l n then l - (push_bit n 2) else l)\<close>
proof -
  have *: \<open>(k AND mask (Suc n)) - 2 * 2 ^ n = k AND mask (Suc n) OR NOT (mask (Suc n))\<close>
    apply (subst disjunctive_add [symmetric])
    apply (simp_all add: bit_and_iff bit_mask_iff bit_not_iff)
    apply (simp flip: minus_exp_eq_not_mask)
    done
  show ?thesis
    by (rule bit_eqI)
     (auto simp add: Let_def bit_and_iff bit_signed_take_bit_iff push_bit_eq_mult min_def not_le bit_mask_iff bit_exp_iff less_Suc_eq * bit_or_iff bit_not_iff)
qed


subsection \<open>Instance \<^typ>\<open>nat\<close>\<close>

instantiation nat :: semiring_bit_operations
begin

definition and_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m AND n = nat (int m AND int n)\<close> for m n :: nat

definition or_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m OR n = nat (int m OR int n)\<close> for m n :: nat

definition xor_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m XOR n = nat (int m XOR int n)\<close> for m n :: nat

instance proof
  fix m n q :: nat
  show \<open>bit (m AND n) q \<longleftrightarrow> bit m q \<and> bit n q\<close>
    by (auto simp add: and_nat_def bit_and_iff less_le bit_eq_iff)
  show \<open>bit (m OR n) q \<longleftrightarrow> bit m q \<or> bit n q\<close>
    by (auto simp add: or_nat_def bit_or_iff less_le bit_eq_iff)
  show \<open>bit (m XOR n) q \<longleftrightarrow> bit m q \<noteq> bit n q\<close>
    by (auto simp add: xor_nat_def bit_xor_iff less_le bit_eq_iff)
qed

end

lemma and_nat_rec:
  \<open>m AND n = of_bool (odd m \<and> odd n) + 2 * ((m div 2) AND (n div 2))\<close> for m n :: nat
  by (simp add: and_nat_def and_int_rec [of \<open>int m\<close> \<open>int n\<close>] zdiv_int nat_add_distrib nat_mult_distrib)

lemma or_nat_rec:
  \<open>m OR n = of_bool (odd m \<or> odd n) + 2 * ((m div 2) OR (n div 2))\<close> for m n :: nat
  by (simp add: or_nat_def or_int_rec [of \<open>int m\<close> \<open>int n\<close>] zdiv_int nat_add_distrib nat_mult_distrib)

lemma xor_nat_rec:
  \<open>m XOR n = of_bool (odd m \<noteq> odd n) + 2 * ((m div 2) XOR (n div 2))\<close> for m n :: nat
  by (simp add: xor_nat_def xor_int_rec [of \<open>int m\<close> \<open>int n\<close>] zdiv_int nat_add_distrib nat_mult_distrib)

lemma Suc_0_and_eq [simp]:
  \<open>Suc 0 AND n = n mod 2\<close>
  using one_and_eq [of n] by simp

lemma and_Suc_0_eq [simp]:
  \<open>n AND Suc 0 = n mod 2\<close>
  using and_one_eq [of n] by simp

lemma Suc_0_or_eq:
  \<open>Suc 0 OR n = n + of_bool (even n)\<close>
  using one_or_eq [of n] by simp

lemma or_Suc_0_eq:
  \<open>n OR Suc 0 = n + of_bool (even n)\<close>
  using or_one_eq [of n] by simp

lemma Suc_0_xor_eq:
  \<open>Suc 0 XOR n = n + of_bool (even n) - of_bool (odd n)\<close>
  using one_xor_eq [of n] by simp

lemma xor_Suc_0_eq:
  \<open>n XOR Suc 0 = n + of_bool (even n) - of_bool (odd n)\<close>
  using xor_one_eq [of n] by simp


subsection \<open>Instances for \<^typ>\<open>integer\<close> and \<^typ>\<open>natural\<close>\<close>

unbundle integer.lifting natural.lifting

instantiation integer :: ring_bit_operations
begin

lift_definition not_integer :: \<open>integer \<Rightarrow> integer\<close>
  is not .

lift_definition and_integer :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is \<open>and\<close> .

lift_definition or_integer :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is or .

lift_definition xor_integer ::  \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is xor .

instance proof
  fix k l :: \<open>integer\<close> and n :: nat
  show \<open>- k = NOT (k - 1)\<close>
    by transfer (simp add: minus_eq_not_minus_1)
  show \<open>bit (NOT k) n \<longleftrightarrow> (2 :: integer) ^ n \<noteq> 0 \<and> \<not> bit k n\<close>
    by transfer (fact bit_not_iff)
  show \<open>bit (k AND l) n \<longleftrightarrow> bit k n \<and> bit l n\<close>
    by transfer (fact bit_and_iff)
  show \<open>bit (k OR l) n \<longleftrightarrow> bit k n \<or> bit l n\<close>
    by transfer (fact bit_or_iff)
  show \<open>bit (k XOR l) n \<longleftrightarrow> bit k n \<noteq> bit l n\<close>
    by transfer (fact bit_xor_iff)
qed

end

instantiation natural :: semiring_bit_operations
begin

lift_definition and_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>and\<close> .

lift_definition or_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is or .

lift_definition xor_natural ::  \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is xor .

instance proof
  fix m n :: \<open>natural\<close> and q :: nat
  show \<open>bit (m AND n) q \<longleftrightarrow> bit m q \<and> bit n q\<close>
    by transfer (fact bit_and_iff)
  show \<open>bit (m OR n) q \<longleftrightarrow> bit m q \<or> bit n q\<close>
    by transfer (fact bit_or_iff)
  show \<open>bit (m XOR n) q \<longleftrightarrow> bit m q \<noteq> bit n q\<close>
    by transfer (fact bit_xor_iff)
qed

end

lifting_update integer.lifting
lifting_forget integer.lifting

lifting_update natural.lifting
lifting_forget natural.lifting


subsection \<open>Key ideas of bit operations\<close>

text \<open>
  When formalizing bit operations, it is tempting to represent
  bit values as explicit lists over a binary type. This however
  is a bad idea, mainly due to the inherent ambiguities in
  representation concerning repeating leading bits.

  Hence this approach avoids such explicit lists altogether
  following an algebraic path:

  \<^item> Bit values are represented by numeric types: idealized
    unbounded bit values can be represented by type \<^typ>\<open>int\<close>,
    bounded bit values by quotient types over \<^typ>\<open>int\<close>.

  \<^item> (A special case are idealized unbounded bit values ending
    in @{term [source] 0} which can be represented by type \<^typ>\<open>nat\<close> but
    only support a restricted set of operations).

  \<^item> From this idea follows that

      \<^item> multiplication by \<^term>\<open>2 :: int\<close> is a bit shift to the left and

      \<^item> division by \<^term>\<open>2 :: int\<close> is a bit shift to the right.

  \<^item> Concerning bounded bit values, iterated shifts to the left
    may result in eliminating all bits by shifting them all
    beyond the boundary.  The property \<^prop>\<open>(2 :: int) ^ n \<noteq> 0\<close>
    represents that \<^term>\<open>n\<close> is \<^emph>\<open>not\<close> beyond that boundary.

  \<^item> The projection on a single bit is then @{thm bit_iff_odd [where ?'a = int, no_vars]}.

  \<^item> This leads to the most fundamental properties of bit values:

      \<^item> Equality rule: @{thm bit_eqI [where ?'a = int, no_vars]}

      \<^item> Induction rule: @{thm bits_induct [where ?'a = int, no_vars]}

  \<^item> Typical operations are characterized as follows:

      \<^item> Singleton \<^term>\<open>n\<close>th bit: \<^term>\<open>(2 :: int) ^ n\<close>

      \<^item> Bit mask upto bit \<^term>\<open>n\<close>: @{thm mask_eq_exp_minus_1 [where ?'a = int, no_vars]}

      \<^item> Left shift: @{thm push_bit_eq_mult [where ?'a = int, no_vars]}

      \<^item> Right shift: @{thm drop_bit_eq_div [where ?'a = int, no_vars]}

      \<^item> Truncation: @{thm take_bit_eq_mod [where ?'a = int, no_vars]}

      \<^item> Negation: @{thm bit_not_iff [where ?'a = int, no_vars]}

      \<^item> And: @{thm bit_and_iff [where ?'a = int, no_vars]}

      \<^item> Or: @{thm bit_or_iff [where ?'a = int, no_vars]}

      \<^item> Xor: @{thm bit_xor_iff [where ?'a = int, no_vars]}

      \<^item> Set a single bit: @{thm set_bit_def [where ?'a = int, no_vars]}

      \<^item> Unset a single bit: @{thm unset_bit_def [where ?'a = int, no_vars]}

      \<^item> Flip a single bit: @{thm flip_bit_def [where ?'a = int, no_vars]}
\<close>

end
