theory Examples2
imports Examples
begin

text {* This is achieved by unfolding suitable equations during
  interpretation.  These equations are given after the keyword
  \isakeyword{where} and require proofs.  The revised command
  that replaces @{text "\<sqsubset>"} by @{text "<"}, is: *}

interpretation %visible nat: partial_order "op \<le> :: [nat, nat] \<Rightarrow> bool"
  where "partial_order.less op \<le> (x::nat) y = (x < y)"
proof -
  txt {* The goals are @{subgoals [display]}
    The proof that @{text \<le>} is a partial order is as above. *}
  show "partial_order (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
    by unfold_locales auto
  txt {* The second goal is shown by unfolding the
    definition of @{term "partial_order.less"}. *}
  show "partial_order.less op \<le> (x::nat) y = (x < y)"
    unfolding partial_order.less_def [OF `partial_order op \<le>`]
    by auto
qed

text {* Note that the above proof is not in the context of a locale.
  Hence, the correct interpretation of @{text
  "partial_order.less_def"} is obtained manually with @{text OF}.
  *}

end
