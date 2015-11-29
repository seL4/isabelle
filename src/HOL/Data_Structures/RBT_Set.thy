(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Sets\<close>

theory RBT_Set
imports
  RBT
  Cmp
  Isin2
begin

fun ins :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"ins x Leaf = R Leaf x Leaf" |
"ins x (B l a r) =
  (case cmp x a of
     LT \<Rightarrow> bal (ins x l) a r |
     GT \<Rightarrow> bal l a (ins x r) |
     EQ \<Rightarrow> B l a r)" |
"ins x (R l a r) =
  (case cmp x a of
    LT \<Rightarrow> R (ins x l) a r |
    GT \<Rightarrow> R l a (ins x r) |
    EQ \<Rightarrow> R l a r)"

definition insert :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"insert x t = paint Black (ins x t)"

fun del :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and delL :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and delR :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
where
"del x Leaf = Leaf" |
"del x (Node _ l a r) =
  (case cmp x a of
     LT \<Rightarrow> delL x l a r |
     GT \<Rightarrow> delR x l a r |
     EQ \<Rightarrow> combine l r)" |
"delL x (B t1 a t2) b t3 = balL (del x (B t1 a t2)) b t3" |
"delL x l a r = R (del x l) a r" |
"delR x t1 a (B t2 b t3) = balR t1 a (del x (B t2 b t3))" | 
"delR x l a r = R l a (del x r)"

definition delete :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

lemma inorder_paint: "inorder(paint c t) = inorder t"
by(induction t) (auto)

lemma inorder_bal:
  "inorder(bal l a r) = inorder l @ a # inorder r"
by(induction l a r rule: bal.induct) (auto)

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(ins x t) = ins_list x (inorder t)"
by(induction x t rule: ins.induct) (auto simp: ins_list_simps inorder_bal)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (simp add: insert_def inorder_ins inorder_paint)

lemma inorder_balL:
  "inorder(balL l a r) = inorder l @ a # inorder r"
by(induction l a r rule: balL.induct)(auto simp: inorder_bal inorder_paint)

lemma inorder_balR:
  "inorder(balR l a r) = inorder l @ a # inorder r"
by(induction l a r rule: balR.induct) (auto simp: inorder_bal inorder_paint)

lemma inorder_combine:
  "inorder(combine l r) = inorder l @ inorder r"
by(induction l r rule: combine.induct)
  (auto simp: inorder_balL inorder_balR split: tree.split color.split)

lemma inorder_del:
 "sorted(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
 "sorted(inorder l) \<Longrightarrow>  inorder(delL x l a r) =
    del_list x (inorder l) @ a # inorder r"
 "sorted(inorder r) \<Longrightarrow>  inorder(delR x l a r) =
    inorder l @ a # del_list x (inorder r)"
by(induction x t and x l a r and x l a r rule: del_delL_delR.induct)
  (auto simp: del_list_simps inorder_combine inorder_balL inorder_balR)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by (auto simp: delete_def inorder_del inorder_paint)


interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto


subsection \<open>Structural invariants\<close>

fun color :: "'a rbt \<Rightarrow> color" where
"color Leaf = Black" |
"color (Node c _ _ _) = c"

fun bheight :: "'a rbt \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node c l x r) = (if c = Black then Suc(bheight l) else bheight l)"

fun inv1 :: "'a rbt \<Rightarrow> bool" where
"inv1 Leaf = True" |
"inv1 (Node c l a r) =
  (inv1 l \<and> inv1 r \<and> (c = Black \<or> color l = Black \<and> color r = Black))"

fun inv1_root :: "'a rbt \<Rightarrow> bool" \<comment> \<open>Weaker version\<close> where
"inv1_root Leaf = True" |
"inv1_root (Node c l a r) = (inv1 l \<and> inv1 r)"

fun inv2 :: "'a rbt \<Rightarrow> bool" where
"inv2 Leaf = True" |
"inv2 (Node c l x r) = (inv2 l \<and> inv2 r \<and> bheight l = bheight r)"

lemma inv1_rootI[simp]: "inv1 t \<Longrightarrow> inv1_root t"
by (cases t) simp+

definition rbt :: "'a rbt \<Rightarrow> bool" where
"rbt t = (inv1 t \<and> inv2 t \<and> color t = Black)"

lemma color_paint_Black: "color (paint Black t) = Black"
by (cases t) auto

theorem rbt_Leaf: "rbt Leaf"
by (simp add: rbt_def)

lemma paint_inv1_root: "inv1_root t \<Longrightarrow> inv1_root (paint c t)"
by (cases t) auto

lemma inv1_paint_Black: "inv1_root t \<Longrightarrow> inv1 (paint Black t)"
by (cases t) auto

lemma inv2_paint: "inv2 t \<Longrightarrow> inv2 (paint c t)"
by (cases t) auto

lemma inv1_bal: "\<lbrakk>inv1_root l; inv1_root r\<rbrakk> \<Longrightarrow> inv1 (bal l a r)" 
by (induct l a r rule: bal.induct) auto

lemma bheight_bal:
  "bheight l = bheight r \<Longrightarrow> bheight (bal l a r) = Suc (bheight l)"
by (induct l a r rule: bal.induct) auto

lemma inv2_bal: 
  "\<lbrakk> inv2 l; inv2 r; bheight l = bheight r \<rbrakk> \<Longrightarrow> inv2 (bal l a r)"
by (induct l a r rule: bal.induct) auto


subsubsection \<open>Insertion\<close>

lemma inv1_ins: assumes "inv1 t"
  shows "color t = Black \<Longrightarrow> inv1 (ins x t)" "inv1_root (ins x t)"
using assms
by (induct x t rule: ins.induct) (auto simp: inv1_bal)

lemma inv2_ins: assumes "inv2 t"
  shows "inv2 (ins x t)" "bheight (ins x t) = bheight t"
using assms
by (induct x t rule: ins.induct) (auto simp: inv2_bal bheight_bal)

theorem rbt_ins: "rbt t \<Longrightarrow> rbt (insert x t)"
by (simp add: inv1_ins inv2_ins color_paint_Black inv1_paint_Black inv2_paint
  rbt_def insert_def)

(*
lemma bheight_paintR'[simp]: "color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
by (cases t) auto

lemma balL_inv2_with_inv1:
  assumes "inv2 lt" "inv2 rt" "bheight lt + 1 = bheight rt" "inv1 rt"
  shows "bheight (balL lt a rt) = bheight lt + 1"  "inv2 (balL lt a rt)"
using assms 
by (induct lt a rt rule: balL.induct) (auto simp: inv2_bal inv2_paint bheight_bal)

lemma balL_inv2_app: 
  assumes "inv2 lt" "inv2 rt" "bheight lt + 1 = bheight rt" "color rt = Black"
  shows "inv2 (balL lt a rt)" 
        "bheight (balL lt a rt) = bheight rt"
using assms 
by (induct lt a rt rule: balL.induct) (auto simp add: inv2_bal bheight_bal) 

lemma balL_inv1: "\<lbrakk>inv1_root l; inv1 r; color r = Black\<rbrakk> \<Longrightarrow> inv1 (balL l a r)"
by (induct l a r rule: balL.induct) (simp_all add: inv1_bal)

lemma balL_inv1_root: "\<lbrakk> inv1_root lt; inv1 rt \<rbrakk> \<Longrightarrow> inv1_root (balL lt a rt)"
by (induct lt a rt rule: balL.induct) (auto simp: inv1_bal paint_inv1_root)

lemma balR_inv2_with_inv1:
  assumes "inv2 lt" "inv2 rt" "bheight lt = bheight rt + 1" "inv1 lt"
  shows "inv2 (balR lt a rt) \<and> bheight (balR lt a rt) = bheight lt"
using assms
by(induct lt a rt rule: balR.induct)(auto simp: inv2_bal bheight_bal inv2_paint)

lemma balR_inv1: "\<lbrakk>inv1 a; inv1_root b; color a = Black\<rbrakk> \<Longrightarrow> inv1 (balR a x b)"
by (induct a x b rule: balR.induct) (simp_all add: inv1_bal)

lemma balR_inv1_root: "\<lbrakk> inv1 lt; inv1_root rt \<rbrakk> \<Longrightarrow>inv1_root (balR lt x rt)"
by (induct lt x rt rule: balR.induct) (auto simp: inv1_bal paint_inv1_root)

lemma combine_inv2:
  assumes "inv2 lt" "inv2 rt" "bheight lt = bheight rt"
  shows "bheight (combine lt rt) = bheight lt" "inv2 (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct) 
   (auto simp: balL_inv2_app split: tree.splits color.splits)

lemma combine_inv1: 
  assumes "inv1 lt" "inv1 rt"
  shows "color lt = Black \<Longrightarrow> color rt = Black \<Longrightarrow> inv1 (combine lt rt)"
         "inv1_root (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct)
   (auto simp: balL_inv1 split: tree.splits color.splits)


lemma 
  assumes "inv2 lt" "inv1 lt"
  shows
  "\<lbrakk>inv2 rt; bheight lt = bheight rt; inv1 rt\<rbrakk> \<Longrightarrow>
   inv2 (rbt_del_from_left x lt k v rt) \<and> 
   bheight (rbt_del_from_left x lt k v rt) = bheight lt \<and> 
   (color_of lt = B \<and> color_of rt = B \<and> inv1 (rbt_del_from_left x lt k v rt) \<or> 
    (color_of lt \<noteq> B \<or> color_of rt \<noteq> B) \<and> inv1l (rbt_del_from_left x lt k v rt))"
  and "\<lbrakk>inv2 rt; bheight lt = bheight rt; inv1 rt\<rbrakk> \<Longrightarrow>
  inv2 (rbt_del_from_right x lt k v rt) \<and> 
  bheight (rbt_del_from_right x lt k v rt) = bheight lt \<and> 
  (color_of lt = B \<and> color_of rt = B \<and> inv1 (rbt_del_from_right x lt k v rt) \<or> 
   (color_of lt \<noteq> B \<or> color_of rt \<noteq> B) \<and> inv1l (rbt_del_from_right x lt k v rt))"
  and rbt_del_inv1_inv2: "inv2 (rbt_del x lt) \<and> (color_of lt = R \<and> bheight (rbt_del x lt) = bheight lt \<and> inv1 (rbt_del x lt) 
  \<or> color_of lt = B \<and> bheight (rbt_del x lt) = bheight lt - 1 \<and> inv1l (rbt_del x lt))"
using assms
proof (induct x lt k v rt and x lt k v rt and x lt rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
case (2 y c _ y')
  have "y = y' \<or> y < y' \<or> y > y'" by auto
  thus ?case proof (elim disjE)
    assume "y = y'"
    with 2 show ?thesis by (cases c) (simp add: combine_inv2 combine_inv1)+
  next
    assume "y < y'"
    with 2 show ?thesis by (cases c) auto
  next
    assume "y' < y"
    with 2 show ?thesis by (cases c) auto
  qed
next
  case (3 y lt z v rta y' ss bb) 
  thus ?case by (cases "color_of (Branch B lt z v rta) = B \<and> color_of bb = B") (simp add: balance_left_inv2_with_inv1 balance_left_inv1 balance_left_inv1l)+
next
  case (5 y a y' ss lt z v rta)
  thus ?case by (cases "color_of a = B \<and> color_of (Branch B lt z v rta) = B") (simp add: balance_right_inv2_with_inv1 balance_right_inv1 balance_right_inv1l)+
next
  case ("6_1" y a y' ss) thus ?case by (cases "color_of a = B \<and> color_of Empty = B") simp+
qed auto

theorem rbt_delete_is_rbt [simp]: assumes "rbt t" shows "rbt (delete k t)"
proof -
  from assms have "inv2 t" and "inv1 t" unfolding rbt_def by auto 
  hence "inv2 (del k t) \<and> (color t = Red \<and> bheight (del k t) = bheight t \<and> inv1 (del k t) \<or> color t = Black \<and> bheight (del k t) = bheight t - 1 \<and> inv1_root (del k t))"
    by (rule rbt_del_inv1_inv2)
  hence "inv2 (del k t) \<and> inv1l (rbt_del k t)" by (cases "color_of t") auto
  with assms show ?thesis
    unfolding is_rbt_def rbt_delete_def
    by (auto intro: paint_rbt_sorted rbt_del_rbt_sorted)
qed
*)
end
