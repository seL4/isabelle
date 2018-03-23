(* Author: Tobias Nipkow *)

section \<open>Implementing Ordered Sets\<close>

theory Set_by_Ordered
imports List_Ins_Del
begin

locale Set =
fixes empty :: "'s"
fixes insert :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes delete :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes isin :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
fixes set :: "'s \<Rightarrow> 'a set"
fixes invar :: "'s \<Rightarrow> bool"
assumes set_empty:    "set empty = {}"
assumes set_isin:     "invar s \<Longrightarrow> isin s x = (x \<in> set s)"
assumes set_insert:   "invar s \<Longrightarrow> set(insert x s) = Set.insert x (set s)"
assumes set_delete:   "invar s \<Longrightarrow> set(delete x s) = set s - {x}"
assumes invar_empty:  "invar empty"
assumes invar_insert: "invar s \<Longrightarrow> invar(insert x s)"
assumes invar_delete: "invar s \<Longrightarrow> invar(delete x s)"

locale Set_by_Ordered =
fixes empty :: "'t"
fixes insert :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 't"
fixes delete :: "'a \<Rightarrow> 't \<Rightarrow> 't"
fixes isin :: "'t \<Rightarrow> 'a \<Rightarrow> bool"
fixes inorder :: "'t \<Rightarrow> 'a list"
fixes inv :: "'t \<Rightarrow> bool"
assumes empty: "inorder empty = []"
assumes isin: "inv t \<and> sorted(inorder t) \<Longrightarrow>
  isin t x = (x \<in> set (inorder t))"
assumes insert: "inv t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(insert x t) = ins_list x (inorder t)"
assumes delete: "inv t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
assumes inv_empty:  "inv empty"
assumes inv_insert: "inv t \<and> sorted(inorder t) \<Longrightarrow> inv(insert x t)"
assumes inv_delete: "inv t \<and> sorted(inorder t) \<Longrightarrow> inv(delete x t)"
begin

sublocale Set
  empty insert delete isin "set o inorder" "\<lambda>t. inv t \<and> sorted(inorder t)"
proof(standard, goal_cases)
  case 1 show ?case by (auto simp: empty)
next
  case 2 thus ?case by(simp add: isin)
next
  case 3 thus ?case by(simp add: insert set_ins_list)
next
  case (4 s x) thus ?case
    using delete[OF 4, of x] by (auto simp: distinct_if_sorted set_del_list_eq)
next
  case 5 thus ?case by(simp add: empty inv_empty)
next
  case 6 thus ?case by(simp add: insert inv_insert sorted_ins_list)
next
  case 7 thus ?case by (auto simp: delete inv_delete sorted_del_list)
qed

end

end
