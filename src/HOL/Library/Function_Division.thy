(*  Title:      HOL/Library/Function_Division.thy
    Author:     Florian Haftmann, TUM
*)

header {* Pointwise instantiation of functions to division *}

theory Function_Division
imports Function_Algebras
begin

subsection {* Syntactic with division *}

instantiation "fun" :: (type, inverse) inverse
begin

definition "inverse f = inverse \<circ> f"

definition "(f / g) = (\<lambda>x. f x / g x)"

instance ..

end

lemma inverse_fun_apply [simp]:
  "inverse f x = inverse (f x)"
  by (simp add: inverse_fun_def)

lemma divide_fun_apply [simp]:
  "(f / g) x = f x / g x"
  by (simp add: divide_fun_def)

text {*
  Unfortunately, we cannot lift this operations to algebraic type
  classes for division: being different from the constant
  zero function @{term "f \<noteq> 0"} is too weak as precondition.
  So we must introduce our own set of lemmas.
*}

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

text {* Feel free to extend this. *}

text {*
  Another possibility would be a reformulation of the division type
  classes to user a @{term zero_free} predicate rather than
  a direct @{term "a \<noteq> 0"} condition.
*}

end

