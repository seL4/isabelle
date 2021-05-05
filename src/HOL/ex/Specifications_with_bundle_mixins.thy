theory Specifications_with_bundle_mixins
  imports "HOL-Combinatorics.Perm"
begin

locale involutory = opening permutation_syntax +
  fixes f :: \<open>'a perm\<close>
  assumes involutory: \<open>\<And>x. f \<langle>$\<rangle> (f \<langle>$\<rangle> x) = x\<close>
begin

lemma
  \<open>f * f = 1\<close>
  using involutory
  by (simp add: perm_eq_iff apply_sequence)

end

context involutory
begin

thm involutory (*syntax from permutation_syntax only present in locale specification and initial block*)

end


class at_most_two_elems = opening permutation_syntax +
  assumes swap_distinct: \<open>a \<noteq> b \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c \<noteq> c\<close>
begin

lemma
  \<open>card (UNIV :: 'a set) \<le> 2\<close>
proof (rule ccontr)
  fix a :: 'a
  assume \<open>\<not> card (UNIV :: 'a set) \<le> 2\<close>
  then have c0: \<open>card (UNIV :: 'a set) \<ge> 3\<close>
    by simp
  then have [simp]: \<open>finite (UNIV :: 'a set)\<close>
    using card.infinite by fastforce
  from c0 card_Diff1_le [of UNIV a]
  have ca: \<open>card (UNIV - {a}) \<ge> 2\<close>
    by simp
  then obtain b where \<open>b \<in> (UNIV - {a})\<close>
    by (metis all_not_in_conv card.empty card_2_iff' le_zero_eq)
  with ca card_Diff1_le [of \<open>UNIV - {a}\<close> b]
  have cb: \<open>card (UNIV - {a, b}) \<ge> 1\<close> and \<open>a \<noteq> b\<close>
    by simp_all
  then obtain c where \<open>c \<in> (UNIV - {a, b})\<close>
    by (metis One_nat_def all_not_in_conv card.empty le_zero_eq nat.simps(3))
  then have \<open>a \<noteq> c\<close> \<open>b \<noteq> c\<close>
    by auto
  with swap_distinct [of a b c] show False
    by (simp add: \<open>a \<noteq> b\<close>) 
qed

end

thm swap_distinct (*syntax from permutation_syntax only present in class specification and initial block*)

end