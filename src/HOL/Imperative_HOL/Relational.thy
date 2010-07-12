theory Relational 
imports Array Ref
begin

lemma crel_option_case:
  assumes "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
  obtains "x = None" "crel n h h' r"
        | y where "x = Some y" "crel (s y) h h' r" 
  using assms unfolding crel_def by (auto split: option.splits)

end
