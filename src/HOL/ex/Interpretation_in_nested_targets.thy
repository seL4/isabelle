theory Interpretation_in_nested_targets
  imports Main
begin

locale injection =
  fixes f :: \<open>'a \<Rightarrow> 'b\<close>
  assumes eqI: \<open>f x = f y \<Longrightarrow> x = y\<close>
begin

lemma eq_iff:
  \<open>x = y \<longleftrightarrow> f x = f y\<close>
  by (auto intro: eqI)

lemma inv_apply:
  \<open>inv f (f x) = x\<close>
  by (rule inv_f_f) (simp add: eqI injI)

end

context
  fixes f :: \<open>'a::linorder \<Rightarrow> 'b::linorder\<close>
  assumes \<open>strict_mono f\<close>
begin

global_interpretation strict_mono: injection f
  by standard (simp add: \<open>strict_mono f\<close> strict_mono_eq)

thm strict_mono.eq_iff
thm strict_mono.inv_apply

end

thm strict_mono.eq_iff
thm strict_mono.inv_apply

end
