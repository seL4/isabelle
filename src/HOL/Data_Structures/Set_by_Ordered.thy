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
assumes "set empty = {}"
assumes "invar s \<Longrightarrow> isin s a = (a \<in> set s)"
assumes "invar s \<Longrightarrow> set(insert a s) = Set.insert a (set s)"
assumes "invar s \<Longrightarrow> set(delete a s) = set s - {a}"
assumes "invar empty"
assumes "invar s \<Longrightarrow> invar(insert a s)"
assumes "invar s \<Longrightarrow> invar(delete a s)"

locale Set_by_Ordered =
fixes empty :: "'t"
fixes insert :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 't"
fixes delete :: "'a \<Rightarrow> 't \<Rightarrow> 't"
fixes isin :: "'t \<Rightarrow> 'a \<Rightarrow> bool"
fixes inorder :: "'t \<Rightarrow> 'a list"
fixes wf :: "'t \<Rightarrow> bool"
assumes empty: "inorder empty = []"
assumes isin: "wf t \<and> sorted(inorder t) \<Longrightarrow>
  isin t a = (a \<in> elems (inorder t))"
assumes insert: "wf t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(insert a t) = ins_list a (inorder t)"
assumes delete: "wf t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(delete a t) = del_list a (inorder t)"
assumes wf_empty:  "wf empty"
assumes wf_insert: "wf t \<and> sorted(inorder t) \<Longrightarrow> wf(insert a t)"
assumes wf_delete: "wf t \<and> sorted(inorder t) \<Longrightarrow> wf(delete a t)"
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
  case (4 s a) show ?case
    using delete[OF 4, of a] 4 by (auto simp: distinct_if_sorted)
next
  case 5 thus ?case by(simp add: empty wf_empty)
next
  case 6 thus ?case by(simp add: insert wf_insert sorted_ins_list)
next
  case 7 thus ?case by (auto simp: delete wf_delete sorted_del_list)
qed

end

end
