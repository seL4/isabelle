(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for purely algebraically founded lists of bits\<close>

theory Bit_Operations
  imports
    "HOL-Library.Boolean_Algebra"
    Main
begin

subsection \<open>Bit operations in suitable algebraic structures\<close>

class semiring_bit_operations = semiring_bit_shifts +
  fixes "and" :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr "AND" 64)
    and or :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr "OR"  59)
    and xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr "XOR" 59)
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

definition map_bit :: \<open>nat \<Rightarrow> (bool \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>map_bit n f a = take_bit n a + push_bit n (of_bool (f (bit a n)) + 2 * drop_bit (Suc n) a)\<close>

definition set_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>set_bit n = map_bit n top\<close>

definition unset_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>unset_bit n = map_bit n bot\<close>

definition flip_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>flip_bit n = map_bit n Not\<close>

text \<open>
  Having 
  \<^const>\<open>set_bit\<close>, \<^const>\<open>unset_bit\<close> and \<^const>\<open>flip_bit\<close> as separate
  operations allows to implement them using bit masks later.
\<close>

lemma stable_imp_drop_eq:
  \<open>drop_bit n a = a\<close> if \<open>a div 2 = a\<close>
  by (induction n) (simp_all add: that)

lemma map_bit_0 [simp]:
  \<open>map_bit 0 f a = of_bool (f (odd a)) + 2 * (a div 2)\<close>
  by (simp add: map_bit_def)

lemma map_bit_Suc [simp]:
  \<open>map_bit (Suc n) f a = a mod 2 + 2 * map_bit n f (a div 2)\<close>
  by (auto simp add: map_bit_def algebra_simps mod2_eq_if push_bit_add mult_2
    elim: evenE oddE)

lemma set_bit_0 [simp]:
  \<open>set_bit 0 a = 1 + 2 * (a div 2)\<close>
  by (simp add: set_bit_def)

lemma set_bit_Suc [simp]:
  \<open>set_bit (Suc n) a = a mod 2 + 2 * set_bit n (a div 2)\<close>
  by (simp add: set_bit_def)

lemma unset_bit_0 [simp]:
  \<open>unset_bit 0 a = 2 * (a div 2)\<close>
  by (simp add: unset_bit_def)

lemma unset_bit_Suc [simp]:
  \<open>unset_bit (Suc n) a = a mod 2 + 2 * unset_bit n (a div 2)\<close>
  by (simp add: unset_bit_def)

lemma flip_bit_0 [simp]:
  \<open>flip_bit 0 a = of_bool (even a) + 2 * (a div 2)\<close>
  by (simp add: flip_bit_def)

lemma flip_bit_Suc [simp]:
  \<open>flip_bit (Suc n) a = a mod 2 + 2 * flip_bit n (a div 2)\<close>
  by (simp add: flip_bit_def)

sublocale "and": semilattice \<open>(AND)\<close>
  by standard (auto simp add: bit_eq_iff bit_and_iff)

sublocale or: semilattice_neutr \<open>(OR)\<close> 0
  by standard (auto simp add: bit_eq_iff bit_or_iff)

sublocale xor: comm_monoid \<open>(XOR)\<close> 0
  by standard (auto simp add: bit_eq_iff bit_xor_iff)

lemma zero_and_eq [simp]:
  "0 AND a = 0"
  by (simp add: bit_eq_iff bit_and_iff)

lemma and_zero_eq [simp]:
  "a AND 0 = 0"
  by (simp add: bit_eq_iff bit_and_iff)

lemma one_and_eq [simp]:
  "1 AND a = of_bool (odd a)"
  by (simp add: bit_eq_iff bit_and_iff) (auto simp add: bit_1_iff)

lemma and_one_eq [simp]:
  "a AND 1 = of_bool (odd a)"
  using one_and_eq [of a] by (simp add: ac_simps)

lemma one_or_eq [simp]:
  "1 OR a = a + of_bool (even a)"
  by (simp add: bit_eq_iff bit_or_iff add.commute [of _ 1] even_bit_succ_iff) (auto simp add: bit_1_iff)

lemma or_one_eq [simp]:
  "a OR 1 = a + of_bool (even a)"
  using one_or_eq [of a] by (simp add: ac_simps)

lemma one_xor_eq [simp]:
  "1 XOR a = a + of_bool (even a) - of_bool (odd a)"
  by (simp add: bit_eq_iff bit_xor_iff add.commute [of _ 1] even_bit_succ_iff) (auto simp add: bit_1_iff odd_bit_iff_bit_pred elim: oddE)

lemma xor_one_eq [simp]:
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
  apply (auto simp add: bit_eq_iff bit_and_iff)
  apply (simp add: bit_exp_iff)
  apply (metis local.bit_def local.bit_exp_iff local.bits_div_by_0)
  done

sublocale bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
  rewrites \<open>bit.xor = (XOR)\<close>
proof -
  interpret bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
    apply standard
         apply simp_all
       apply (auto simp add: bit_eq_iff bit_and_iff bit_or_iff bit_not_iff)
    apply (simp add: bit_exp_iff)
    apply (metis local.bit_def local.bit_exp_iff local.bits_div_by_0)
    done
  show \<open>boolean_algebra (AND) (OR) NOT 0 (- 1)\<close>
    by standard
  show \<open>boolean_algebra.xor (AND) (OR) NOT = (XOR)\<close> 
    apply (auto simp add: fun_eq_iff bit.xor_def bit_eq_iff bit_and_iff bit_or_iff bit_not_iff bit_xor_iff)
         apply (simp_all add: bit_exp_iff, simp_all add: bit_def)
        apply (metis local.bit_exp_iff local.bits_div_by_0)
       apply (metis local.bit_exp_iff local.bits_div_by_0)
    done
qed

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

end


subsubsection \<open>Instance \<^typ>\<open>nat\<close>\<close>

locale zip_nat = single: abel_semigroup f
    for f :: "bool \<Rightarrow> bool \<Rightarrow> bool"  (infixl \<open>\<^bold>*\<close> 70) +
  assumes end_of_bits: \<open>\<not> False \<^bold>* False\<close>
begin

function F :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>  (infixl \<open>\<^bold>\<times>\<close> 70)
  where \<open>m \<^bold>\<times> n = (if m = 0 \<and> n = 0 then 0
    else of_bool (odd m \<^bold>* odd n) + 2 * ((m div 2) \<^bold>\<times> (n div 2)))\<close>
  by auto

termination
  by (relation "measure (case_prod (+))") auto

declare F.simps [simp del]

lemma rec:
  "m \<^bold>\<times> n = of_bool (odd m \<^bold>* odd n) + (m div 2) \<^bold>\<times> (n div 2) * 2"
proof (cases \<open>m = 0 \<and> n = 0\<close>)
  case True
  then have \<open>m \<^bold>\<times> n = 0\<close>
    using True by (simp add: F.simps [of 0 0])
  moreover have \<open>(m div 2) \<^bold>\<times> (n div 2) = m \<^bold>\<times> n\<close>
    using True by simp
  ultimately show ?thesis
    using True by (simp add: end_of_bits)
next
  case False
  then show ?thesis
    by (auto simp add: ac_simps F.simps [of m n])
qed

lemma bit_eq_iff:
  \<open>bit (m \<^bold>\<times> n) q \<longleftrightarrow> bit m q \<^bold>* bit n q\<close>
proof (induction q arbitrary: m n)
  case 0
  then show ?case
    by (simp add: rec [of m n])
next
  case (Suc n)
  then show ?case
    by (simp add: rec [of m n])
qed

sublocale abel_semigroup F
  by standard (simp_all add: Parity.bit_eq_iff bit_eq_iff ac_simps)

end

instantiation nat :: semiring_bit_operations
begin

global_interpretation and_nat: zip_nat \<open>(\<and>)\<close>
  defines and_nat = and_nat.F
  by standard auto

global_interpretation and_nat: semilattice \<open>(AND) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close>
proof (rule semilattice.intro, fact and_nat.abel_semigroup_axioms, standard)
  show \<open>n AND n = n\<close> for n :: nat
    by (simp add: bit_eq_iff and_nat.bit_eq_iff)
qed

global_interpretation or_nat: zip_nat \<open>(\<or>)\<close>
  defines or_nat = or_nat.F
  by standard auto

global_interpretation or_nat: semilattice \<open>(OR) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close>
proof (rule semilattice.intro, fact or_nat.abel_semigroup_axioms, standard)
  show \<open>n OR n = n\<close> for n :: nat
    by (simp add: bit_eq_iff or_nat.bit_eq_iff)
qed

global_interpretation xor_nat: zip_nat \<open>(\<noteq>)\<close>
  defines xor_nat = xor_nat.F
  by standard auto

instance proof
  fix m n q :: nat
  show \<open>bit (m AND n) q \<longleftrightarrow> bit m q \<and> bit n q\<close>
    by (fact and_nat.bit_eq_iff)
  show \<open>bit (m OR n) q \<longleftrightarrow> bit m q \<or> bit n q\<close>
    by (fact or_nat.bit_eq_iff)
  show \<open>bit (m XOR n) q \<longleftrightarrow> bit m q \<noteq> bit n q\<close>
    by (fact xor_nat.bit_eq_iff)
qed

end

lemma Suc_0_and_eq [simp]:
  \<open>Suc 0 AND n = of_bool (odd n)\<close>
  using one_and_eq [of n] by simp

lemma and_Suc_0_eq [simp]:
  \<open>n AND Suc 0 = of_bool (odd n)\<close>
  using and_one_eq [of n] by simp

lemma Suc_0_or_eq [simp]:
  \<open>Suc 0 OR n = n + of_bool (even n)\<close>
  using one_or_eq [of n] by simp

lemma or_Suc_0_eq [simp]:
  \<open>n OR Suc 0 = n + of_bool (even n)\<close>
  using or_one_eq [of n] by simp

lemma Suc_0_xor_eq [simp]:
  \<open>Suc 0 XOR n = n + of_bool (even n) - of_bool (odd n)\<close>
  using one_xor_eq [of n] by simp

lemma xor_Suc_0_eq [simp]:
  \<open>n XOR Suc 0 = n + of_bool (even n) - of_bool (odd n)\<close>
  using xor_one_eq [of n] by simp


subsubsection \<open>Instance \<^typ>\<open>int\<close>\<close>

locale zip_int = single: abel_semigroup f
  for f :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>  (infixl \<open>\<^bold>*\<close> 70)
begin

function F :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>\<^bold>\<times>\<close> 70)
  where \<open>k \<^bold>\<times> l = (if k \<in> {0, - 1} \<and> l \<in> {0, - 1}
    then - of_bool (odd k \<^bold>* odd l)
    else of_bool (odd k \<^bold>* odd l) + 2 * ((k div 2) \<^bold>\<times> (l div 2)))\<close>
  by auto

termination
  by (relation "measure (\<lambda>(k, l). nat (\<bar>k\<bar> + \<bar>l\<bar>))") auto

declare F.simps [simp del]

lemma rec:
  \<open>k \<^bold>\<times> l = of_bool (odd k \<^bold>* odd l) + 2 * ((k div 2) \<^bold>\<times> (l div 2))\<close>
proof (cases \<open>k \<in> {0, - 1} \<and> l \<in> {0, - 1}\<close>)
  case True
  then have \<open>(k div 2) \<^bold>\<times> (l div 2) = k \<^bold>\<times> l\<close>
    by auto
  moreover have \<open>of_bool (odd k \<^bold>* odd l) = - (k \<^bold>\<times> l)\<close>
    using True by (simp add: F.simps [of k l])
  ultimately show ?thesis by simp
next
  case False
  then show ?thesis
    by (auto simp add: ac_simps F.simps [of k l])
qed

lemma bit_eq_iff:
  \<open>bit (k \<^bold>\<times> l) n \<longleftrightarrow> bit k n \<^bold>* bit l n\<close>
proof (induction n arbitrary: k l)
  case 0
  then show ?case
    by (simp add: rec [of k l])
next
  case (Suc n)
  then show ?case
    by (simp add: rec [of k l])
qed

sublocale abel_semigroup F
  by standard (simp_all add: Parity.bit_eq_iff bit_eq_iff ac_simps)

end

instantiation int :: ring_bit_operations
begin

global_interpretation and_int: zip_int "(\<and>)"
  defines and_int = and_int.F
  by standard

global_interpretation and_int: semilattice "(AND) :: int \<Rightarrow> int \<Rightarrow> int"
proof (rule semilattice.intro, fact and_int.abel_semigroup_axioms, standard)
  show "k AND k = k" for k :: int
    by (simp add: bit_eq_iff and_int.bit_eq_iff)
qed

global_interpretation or_int: zip_int "(\<or>)"
  defines or_int = or_int.F
  by standard

global_interpretation or_int: semilattice "(OR) :: int \<Rightarrow> int \<Rightarrow> int"
proof (rule semilattice.intro, fact or_int.abel_semigroup_axioms, standard)
  show "k OR k = k" for k :: int
    by (simp add: bit_eq_iff or_int.bit_eq_iff)
qed

global_interpretation xor_int: zip_int "(\<noteq>)"
  defines xor_int = xor_int.F
  by standard

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

lemma bit_not_iff_int:
  \<open>bit (NOT k) n \<longleftrightarrow> \<not> bit k n\<close>
    for k :: int
  by (induction n arbitrary: k) (simp_all add: not_int_div_2 even_not_iff_int)

instance proof
  fix k l :: int and n :: nat
  show \<open>- k = NOT (k - 1)\<close>
    by (simp add: not_int_def)
  show \<open>bit (k AND l) n \<longleftrightarrow> bit k n \<and> bit l n\<close>
    by (fact and_int.bit_eq_iff)
  show \<open>bit (k OR l) n \<longleftrightarrow> bit k n \<or> bit l n\<close>
    by (fact or_int.bit_eq_iff)
  show \<open>bit (k XOR l) n \<longleftrightarrow> bit k n \<noteq> bit l n\<close>
    by (fact xor_int.bit_eq_iff)
qed (simp_all add: bit_not_iff_int)

end

end
