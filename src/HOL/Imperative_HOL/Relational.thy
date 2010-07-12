theory Relational 
imports Array Ref
begin

lemma crel_assert_eq: "(\<And>h h' r. crel f h h' r \<Longrightarrow> P r) \<Longrightarrow> f \<guillemotright>= assert P = f"
unfolding crel_def bind_def Let_def assert_def
  raise_def return_def prod_case_beta
apply (cases f)
apply simp
apply (simp add: expand_fun_eq split_def)
apply (auto split: option.split)
done

lemma crel_option_caseI:
  assumes "\<And>y. x = Some y \<Longrightarrow> crel (s y) h h' r"
  assumes "x = None \<Longrightarrow> crel n h h' r"
  shows "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
using assms
by (auto split: option.split)

lemma crelI2:
  assumes "\<exists>h' rs'. crel f h h' rs' \<and> (\<exists>h'' rs. crel (g rs') h' h'' rs)"
  shows "\<exists>h'' rs. crel (f\<guillemotright>= g) h h'' rs"
  oops

lemma crel_ifI2:
  assumes "c \<Longrightarrow> \<exists>h' r. crel t h h' r"
  "\<not> c \<Longrightarrow> \<exists>h' r. crel e h h' r"
  shows "\<exists> h' r. crel (if c then t else e) h h' r"
  oops

lemma crel_option_case:
  assumes "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
  obtains "x = None" "crel n h h' r"
        | y where "x = Some y" "crel (s y) h h' r" 
  using assms unfolding crel_def by (auto split: option.splits)

end
