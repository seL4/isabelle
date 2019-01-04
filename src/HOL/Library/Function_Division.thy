(*  Title:      HOL/Library/Function_Division.thy
    Author:     Florian Haftmann, TUM
*)

section \<open>Pointwise instantiation of functions to division\<close>

theory Function_Division
imports Function_Algebras
begin

subsection \<open>Syntactic with division\<close>

instantiation "fun" :: (type, inverse) inverse
begin

definition "inverse f = inverse \<circ> f"

definition "f div g = (\<lambda>x. f x / g x)"

instance ..

end

lemma inverse_fun_apply [simp]:
  "inverse f x = inverse (f x)"
  by (simp add: inverse_fun_def)

lemma divide_fun_apply [simp]:
  "(f / g) x = f x / g x"
  by (simp add: divide_fun_def)

text \<open>
  Unfortunately, we cannot lift this operations to algebraic type
  classes for division: being different from the constant
  zero function \<^term>\<open>f \<noteq> 0\<close> is too weak as precondition.
  So we must introduce our own set of lemmas.
\<close>

abbreviation zero_free :: "('b \<Rightarrow> 'a::field) \<Rightarrow> bool" where
  "zero_free f \<equiv> \<not> (\<exists>x. f x = 0)"

lemma fun_left_inverse:
  fixes f :: "'b \<Rightarrow> 'a::field"
  shows "zero_free f \<Longrightarrow> inverse f * f = 1"
  by (simp add: fun_eq_iff)

lemma fun_right_inverse:
  fixes f :: "'b \<Rightarrow> 'a::field"
  shows "zero_free f \<Longrightarrow> f * inverse f = 1"
  by (simp add: fun_eq_iff)

lemma fun_divide_inverse:
  fixes f g :: "'b \<Rightarrow> 'a::field"
  shows "f / g = f * inverse g"
  by (simp add: fun_eq_iff divide_inverse)

text \<open>Feel free to extend this.\<close>

text \<open>
  Another possibility would be a reformulation of the division type
  classes to user a \<^term>\<open>zero_free\<close> predicate rather than
  a direct \<^term>\<open>a \<noteq> 0\<close> condition.
\<close>

end
