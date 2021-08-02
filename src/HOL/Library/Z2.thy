(*  Title:      HOL/Library/Z2.thy
    Author:     Brian Huffman
*)

section \<open>The Field of Integers mod 2\<close>

theory Z2
imports Main
begin

text \<open>
  Note that in most cases \<^typ>\<open>bool\<close> is appropriate when a binary type is needed; the
  type provided here, for historical reasons named \<^text>\<open>bit\<close>, is only needed if proper
  field operations are required.
\<close>

typedef bit = \<open>UNIV :: bool set\<close> ..

instantiation bit :: zero_neq_one
begin

definition zero_bit :: bit
  where \<open>0 = Abs_bit False\<close>

definition one_bit :: bit
  where \<open>1 = Abs_bit True\<close>

instance
  by standard (simp add: zero_bit_def one_bit_def Abs_bit_inject)

end

free_constructors case_bit for \<open>0::bit\<close> | \<open>1::bit\<close>
proof -
  fix P :: bool
  fix a :: bit
  assume \<open>a = 0 \<Longrightarrow> P\<close> and \<open>a = 1 \<Longrightarrow> P\<close>
  then show P
    by (cases a) (auto simp add: zero_bit_def one_bit_def Abs_bit_inject)
qed simp

lemma bit_not_zero_iff [simp]:
  \<open>a \<noteq> 0 \<longleftrightarrow> a = 1\<close> for a :: bit
  by (cases a) simp_all

lemma bit_not_one_imp [simp]:
  \<open>a \<noteq> 1 \<longleftrightarrow> a = 0\<close> for a :: bit
  by (cases a) simp_all

instantiation bit :: semidom_modulo
begin

definition plus_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where \<open>a + b = Abs_bit (Rep_bit a \<noteq> Rep_bit b)\<close>

definition minus_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>minus_bit = plus\<close>

definition times_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where \<open>a * b = Abs_bit (Rep_bit a \<and> Rep_bit b)\<close>

definition divide_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>divide_bit = times\<close>

definition modulo_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where \<open>a mod b = Abs_bit (Rep_bit a \<and> \<not> Rep_bit b)\<close>

instance
  by standard
    (auto simp flip: Rep_bit_inject
    simp add: zero_bit_def one_bit_def plus_bit_def times_bit_def modulo_bit_def Abs_bit_inverse Rep_bit_inverse)

end

lemma bit_2_eq_0 [simp]:
  \<open>2 = (0::bit)\<close>
  by (simp flip: one_add_one add: zero_bit_def plus_bit_def)

instance bit :: semiring_parity
  apply standard
    apply (auto simp flip: Rep_bit_inject simp add: modulo_bit_def Abs_bit_inverse Rep_bit_inverse)
         apply (auto simp add: zero_bit_def one_bit_def Abs_bit_inverse Rep_bit_inverse)
  done

lemma Abs_bit_eq_of_bool [code_abbrev]:
  \<open>Abs_bit = of_bool\<close>
  by (simp add: fun_eq_iff zero_bit_def one_bit_def)

lemma Rep_bit_eq_odd:
  \<open>Rep_bit = odd\<close>
proof -
  have \<open>\<not> Rep_bit 0\<close>
    by (simp only: zero_bit_def) (subst Abs_bit_inverse, auto)
  then show ?thesis
    by (auto simp flip: Rep_bit_inject simp add: fun_eq_iff)
qed

lemma Rep_bit_iff_odd [code_abbrev]:
  \<open>Rep_bit b \<longleftrightarrow> odd b\<close>
  by (simp add: Rep_bit_eq_odd)

lemma Not_Rep_bit_iff_even [code_abbrev]:
  \<open>\<not> Rep_bit b \<longleftrightarrow> even b\<close>
  by (simp add: Rep_bit_eq_odd)

lemma Not_Not_Rep_bit [code_unfold]:
  \<open>\<not> \<not> Rep_bit b \<longleftrightarrow> Rep_bit b\<close>
  by simp

code_datatype \<open>0::bit\<close> \<open>1::bit\<close>

lemma Abs_bit_code [code]:
  \<open>Abs_bit False = 0\<close>
  \<open>Abs_bit True = 1\<close>
  by (simp_all add: Abs_bit_eq_of_bool)

lemma Rep_bit_code [code]:
  \<open>Rep_bit 0 \<longleftrightarrow> False\<close>
  \<open>Rep_bit 1 \<longleftrightarrow> True\<close>
  by (simp_all add: Rep_bit_eq_odd)

context zero_neq_one
begin

abbreviation of_bit :: \<open>bit \<Rightarrow> 'a\<close>
  where \<open>of_bit b \<equiv> of_bool (odd b)\<close>

end

context
begin

qualified lemma bit_eq_iff:
  \<open>a = b \<longleftrightarrow> (even a \<longleftrightarrow> even b)\<close> for a b :: bit
  by (cases a; cases b) simp_all

end

lemma modulo_bit_unfold [simp, code]:
  \<open>a mod b = of_bool (odd a \<and> even b)\<close> for a b :: bit
  by (simp add: modulo_bit_def Abs_bit_eq_of_bool Rep_bit_eq_odd)

lemma power_bit_unfold [simp, code]:
  \<open>a ^ n = of_bool (odd a \<or> n = 0)\<close> for a :: bit
  by (cases a) simp_all

instantiation bit :: semiring_bits
begin

definition bit_bit :: \<open>bit \<Rightarrow> nat \<Rightarrow> bool\<close>
  where [simp]: \<open>bit_bit b n \<longleftrightarrow> odd b \<and> n = 0\<close>

instance
  apply standard
              apply auto
  apply (metis bit.exhaust of_bool_eq(2))
  done

end

instantiation bit :: semiring_bit_shifts
begin

definition push_bit_bit :: \<open>nat \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>push_bit n b = of_bool (odd b \<and> n = 0)\<close> for b :: bit

definition drop_bit_bit :: \<open>nat \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>drop_bit_bit = push_bit\<close>

definition take_bit_bit :: \<open>nat \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>take_bit n b = of_bool (odd b \<and> n > 0)\<close> for b :: bit

instance
  by standard simp_all

end

instantiation bit :: semiring_bit_operations
begin

context
  includes bit_operations_syntax
begin

definition and_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>b AND c = of_bool (odd b \<and> odd c)\<close> for b c :: bit

definition or_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>b OR c = of_bool (odd b \<or> odd c)\<close> for b c :: bit

definition xor_bit :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>b XOR c = of_bool (odd b \<noteq> odd c)\<close> for b c :: bit

definition mask_bit :: \<open>nat \<Rightarrow> bit\<close>
  where [simp]: \<open>mask n = (of_bool (n > 0) :: bit)\<close>

definition set_bit_bit :: \<open>nat \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>set_bit n b = of_bool (n = 0 \<or> odd b)\<close> for b :: bit

definition unset_bit_bit :: \<open>nat \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>unset_bit n b = of_bool (n > 0 \<and> odd b)\<close> for b :: bit

definition flip_bit_bit :: \<open>nat \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>flip_bit n b = of_bool ((n = 0) \<noteq> odd b)\<close> for b :: bit

end

instance
  by standard auto

end

lemma add_bit_eq_xor [simp, code]:
  \<open>(+) = (Bit_Operations.xor :: bit \<Rightarrow> _)\<close>
  by (auto simp add: fun_eq_iff)

lemma mult_bit_eq_and [simp, code]:
  \<open>(*) = (Bit_Operations.and :: bit \<Rightarrow> _)\<close>
  by (simp add: fun_eq_iff)

instantiation bit :: field
begin

definition uminus_bit :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>uminus_bit = id\<close>

definition inverse_bit :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>inverse_bit = id\<close>

instance
  by standard simp_all

end

instantiation bit :: ring_bit_operations
begin

definition not_bit :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>NOT b = of_bool (even b)\<close> for b :: bit

instance
  by standard auto

end

lemma bit_numeral_even [simp]: "numeral (Num.Bit0 w) = (0 :: bit)"
  by (simp only: Z2.bit_eq_iff even_numeral) simp

lemma bit_numeral_odd [simp]: "numeral (Num.Bit1 w) = (1 :: bit)"
  by (simp only: Z2.bit_eq_iff odd_numeral)  simp

end
