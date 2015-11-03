(* Author: Tobias Nipkow *)

section {* Implementing Ordered Sets *}

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
fixes wf :: "'t \<Rightarrow> bool"
assumes empty: "inorder empty = []"
assumes isin: "wf t \<and> sorted(inorder t) \<Longrightarrow>
  isin t x = (x \<in> elems (inorder t))"
assumes insert: "wf t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(insert x t) = ins_list x (inorder t)"
assumes delete: "wf t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
assumes wf_empty:  "wf empty"
assumes wf_insert: "wf t \<and> sorted(inorder t) \<Longrightarrow> wf(insert x t)"
assumes wf_delete: "wf t \<and> sorted(inorder t) \<Longrightarrow> wf(delete x t)"
begin

sublocale Set
  empty insert delete isin "elems o inorder" "\<lambda>t. wf t \<and> sorted(inorder t)"
proof(standard, goal_cases)
  case 1 show ?case by (auto simp: empty)
next
  case 2 thus ?case by(simp add: isin)
next
  case 3 thus ?case by(simp add: insert)
next
  case (4 s x) show ?case
    using delete[OF 4, of x] 4 by (auto simp: distinct_if_sorted)
next
  case 5 thus ?case by(simp add: empty wf_empty)
next
  case 6 thus ?case by(simp add: insert wf_insert sorted_ins_list)
next
  case 7 thus ?case by (auto simp: delete wf_delete sorted_del_list)
qed

end

end
