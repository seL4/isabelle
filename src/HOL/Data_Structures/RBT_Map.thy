(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Maps\<close>

theory RBT_Map
imports
  RBT_Set
  Lookup2
begin

fun upd :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"upd x y Leaf = R Leaf (x,y) Leaf" |
"upd x y (B l (a,b) r) = (case cmp x a of
  LT \<Rightarrow> baliL (upd x y l) (a,b) r |
  GT \<Rightarrow> baliR l (a,b) (upd x y r) |
  EQ \<Rightarrow> B l (x,y) r)" |
"upd x y (R l (a,b) r) = (case cmp x a of
  LT \<Rightarrow> R (upd x y l) (a,b) r |
  GT \<Rightarrow> R l (a,b) (upd x y r) |
  EQ \<Rightarrow> R l (x,y) r)"

definition update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"update x y t = paint Black (upd x y t)"

fun del :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt" where
"del x Leaf = Leaf" |
"del x (Node l (a,b) c r) = (case cmp x a of
     LT \<Rightarrow> if l \<noteq> Leaf \<and> color l = Black
           then baldL (del x l) (a,b) r else R (del x l) (a,b) r |
     GT \<Rightarrow> if r \<noteq> Leaf\<and> color r = Black
           then baldR l (a,b) (del x r) else R l (a,b) (del x r) |
  EQ \<Rightarrow> combine l r)"

definition delete :: "'a::linorder \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

lemma inorder_upd:
  "sorted1(inorder t) \<Longrightarrow> inorder(upd x y t) = upd_list x y (inorder t)"
by(induction x y t rule: upd.induct)
  (auto simp: upd_list_simps inorder_baliL inorder_baliR)

lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by(simp add: update_def inorder_upd inorder_paint)

lemma inorder_del:
 "sorted1(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
by(induction x t rule: del.induct)
  (auto simp: del_list_simps inorder_combine inorder_baldL inorder_baldR)

lemma inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del inorder_paint)


subsection \<open>Structural invariants\<close>

subsubsection \<open>Update\<close>

lemma invc_upd: assumes "invc t"
  shows "color t = Black \<Longrightarrow> invc (upd x y t)" "invc2 (upd x y t)"
using assms
by (induct x y t rule: upd.induct) (auto simp: invc_baliL invc_baliR invc2I)

lemma invh_upd: assumes "invh t"
  shows "invh (upd x y t)" "bheight (upd x y t) = bheight t"
using assms
by(induct x y t rule: upd.induct)
  (auto simp: invh_baliL invh_baliR bheight_baliL bheight_baliR)

theorem rbt_update: "rbt t \<Longrightarrow> rbt (update x y t)"
by (simp add: invc_upd(2) invh_upd(1) color_paint_Black invc_paint_Black invh_paint
  rbt_def update_def)


subsubsection \<open>Deletion\<close>

lemma del_invc_invh: "invh t \<Longrightarrow> invc t \<Longrightarrow> invh (del x t) \<and>
   (color t = Red \<and> bheight (del x t) = bheight t \<and> invc (del x t) \<or>
    color t = Black \<and> bheight (del x t) = bheight t - 1 \<and> invc2 (del x t))"
proof (induct x t rule: del.induct)
case (2 x _ y _ c)
  have "x = y \<or> x < y \<or> x > y" by auto
  thus ?case proof (elim disjE)
    assume "x = y"
    with 2 show ?thesis
    by (cases c) (simp_all add: invh_combine invc_combine)
  next
    assume "x < y"
    with 2 show ?thesis
      by(cases c)
        (auto simp: invh_baldL_invc invc_baldL invc2_baldL dest: neq_LeafD)
  next
    assume "y < x"
    with 2 show ?thesis
      by(cases c)
        (auto simp: invh_baldR_invc invc_baldR invc2_baldR dest: neq_LeafD)
  qed
qed auto

theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete k t)"
by (metis delete_def rbt_def color_paint_Black del_invc_invh invc_paint_Black invc2I invh_paint)

interpretation M: Map_by_Ordered
where empty = empty and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = rbt
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: lookup_map_of)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp add: rbt_def empty_def) 
next
  case 6 thus ?case by (simp add: rbt_update) 
next
  case 7 thus ?case by (simp add: rbt_delete) 
qed

end
