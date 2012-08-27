theory Examples2
imports Examples
begin
text {* \vspace{-5ex} *}
  interpretation %visible int: partial_order "op \<le> :: [int, int] \<Rightarrow> bool"
    where "int.less x y = (x < y)"
  proof -
    txt {* \normalsize The goals are now:
      @{subgoals [display]}
      The proof that~@{text \<le>} is a partial order is as above. *}
    show "partial_order (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)"
      by unfold_locales auto
    txt {* \normalsize The second goal is shown by unfolding the
      definition of @{term "partial_order.less"}. *}
    show "partial_order.less op \<le> x y = (x < y)"
      unfolding partial_order.less_def [OF `partial_order op \<le>`]
      by auto
  qed

text {* Note that the above proof is not in the context of the
  interpreted locale.  Hence, the premise of @{text
  "partial_order.less_def"} is discharged manually with @{text OF}.
  *}
end
