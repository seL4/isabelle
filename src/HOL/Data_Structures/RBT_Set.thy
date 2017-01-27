(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Sets\<close>

theory RBT_Set
imports
  Complex_Main
  RBT
  Cmp
  Isin2
begin

fun ins :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
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

definition insert :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"insert x t = paint Black (ins x t)"

fun del :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and delL :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and delR :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
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

definition delete :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

lemma inorder_paint: "inorder(paint c t) = inorder t"
by(cases t) (auto)

lemma inorder_bal:
  "inorder(bal l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: bal.cases) (auto)

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(ins x t) = ins_list x (inorder t)"
by(induction x t rule: ins.induct) (auto simp: ins_list_simps inorder_bal)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (simp add: insert_def inorder_ins inorder_paint)

lemma inorder_balL:
  "inorder(balL l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: balL.cases)(auto simp: inorder_bal inorder_paint)

lemma inorder_balR:
  "inorder(balR l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: balR.cases) (auto simp: inorder_bal inorder_paint)

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


subsection \<open>Structural invariants\<close>

text\<open>The proofs are due to Markus Reiter and Alexander Krauss.\<close>

fun color :: "'a rbt \<Rightarrow> color" where
"color Leaf = Black" |
"color (Node c _ _ _) = c"

fun bheight :: "'a rbt \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node c l x r) = (if c = Black then bheight l + 1 else bheight l)"

fun invc :: "'a rbt \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node c l a r) =
  (invc l \<and> invc r \<and> (c = Red \<longrightarrow> color l = Black \<and> color r = Black))"

fun invc2 :: "'a rbt \<Rightarrow> bool" \<comment> \<open>Weaker version\<close> where
"invc2 Leaf = True" |
"invc2 (Node c l a r) = (invc l \<and> invc r)"

fun invh :: "'a rbt \<Rightarrow> bool" where
"invh Leaf = True" |
"invh (Node c l x r) = (invh l \<and> invh r \<and> bheight l = bheight r)"

lemma invc2I: "invc t \<Longrightarrow> invc2 t"
by (cases t) simp+

definition rbt :: "'a rbt \<Rightarrow> bool" where
"rbt t = (invc t \<and> invh t \<and> color t = Black)"

lemma color_paint_Black: "color (paint Black t) = Black"
by (cases t) auto

theorem rbt_Leaf: "rbt Leaf"
by (simp add: rbt_def)

lemma paint_invc2: "invc2 t \<Longrightarrow> invc2 (paint c t)"
by (cases t) auto

lemma invc_paint_Black: "invc2 t \<Longrightarrow> invc (paint Black t)"
by (cases t) auto

lemma invh_paint: "invh t \<Longrightarrow> invh (paint c t)"
by (cases t) auto

lemma invc_bal:
  "\<lbrakk>invc l \<and> invc2 r \<or> invc2 l \<and> invc r\<rbrakk> \<Longrightarrow> invc (bal l a r)" 
by (induct l a r rule: bal.induct) auto

lemma bheight_bal:
  "bheight l = bheight r \<Longrightarrow> bheight (bal l a r) = Suc (bheight l)"
by (induct l a r rule: bal.induct) auto

lemma invh_bal: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (bal l a r)"
by (induct l a r rule: bal.induct) auto


subsubsection \<open>Insertion\<close>

lemma invc_ins: assumes "invc t"
  shows "color t = Black \<Longrightarrow> invc (ins x t)" "invc2 (ins x t)"
using assms
by (induct x t rule: ins.induct) (auto simp: invc_bal invc2I)

lemma invh_ins: assumes "invh t"
  shows "invh (ins x t)" "bheight (ins x t) = bheight t"
using assms
by (induct x t rule: ins.induct) (auto simp: invh_bal bheight_bal)

theorem rbt_insert: "rbt t \<Longrightarrow> rbt (insert x t)"
by (simp add: invc_ins invh_ins color_paint_Black invc_paint_Black invh_paint
  rbt_def insert_def)


subsubsection \<open>Deletion\<close>

lemma bheight_paint_Red:
  "color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
by (cases t) auto

lemma balL_invh_with_invc:
  assumes "invh lt" "invh rt" "bheight lt + 1 = bheight rt" "invc rt"
  shows "bheight (balL lt a rt) = bheight lt + 1"  "invh (balL lt a rt)"
using assms 
by (induct lt a rt rule: balL.induct)
   (auto simp: invh_bal invh_paint bheight_bal bheight_paint_Red)

lemma balL_invh_app: 
  assumes "invh lt" "invh rt" "bheight lt + 1 = bheight rt" "color rt = Black"
  shows "invh (balL lt a rt)" 
        "bheight (balL lt a rt) = bheight rt"
using assms 
by (induct lt a rt rule: balL.induct) (auto simp add: invh_bal bheight_bal) 

lemma balL_invc: "\<lbrakk>invc2 l; invc r; color r = Black\<rbrakk> \<Longrightarrow> invc (balL l a r)"
by (induct l a r rule: balL.induct) (simp_all add: invc_bal)

lemma balL_invc2: "\<lbrakk> invc2 lt; invc rt \<rbrakk> \<Longrightarrow> invc2 (balL lt a rt)"
by (induct lt a rt rule: balL.induct) (auto simp: invc_bal paint_invc2 invc2I)

lemma balR_invh_with_invc:
  assumes "invh lt" "invh rt" "bheight lt = bheight rt + 1" "invc lt"
  shows "invh (balR lt a rt) \<and> bheight (balR lt a rt) = bheight lt"
using assms
by(induct lt a rt rule: balR.induct)
  (auto simp: invh_bal bheight_bal invh_paint bheight_paint_Red)

lemma invc_balR: "\<lbrakk>invc a; invc2 b; color a = Black\<rbrakk> \<Longrightarrow> invc (balR a x b)"
by (induct a x b rule: balR.induct) (simp_all add: invc_bal)

lemma invc2_balR: "\<lbrakk> invc lt; invc2 rt \<rbrakk> \<Longrightarrow>invc2 (balR lt x rt)"
by (induct lt x rt rule: balR.induct) (auto simp: invc_bal paint_invc2 invc2I)

lemma invh_combine:
  assumes "invh lt" "invh rt" "bheight lt = bheight rt"
  shows "bheight (combine lt rt) = bheight lt" "invh (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct) 
   (auto simp: balL_invh_app split: tree.splits color.splits)

lemma invc_combine: 
  assumes "invc lt" "invc rt"
  shows "color lt = Black \<Longrightarrow> color rt = Black \<Longrightarrow> invc (combine lt rt)"
         "invc2 (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct)
   (auto simp: balL_invc invc2I split: tree.splits color.splits)


lemma assumes "invh lt" "invc lt"
  shows
  del_invc_invh: "invh (del x lt) \<and> (color lt = Red \<and> bheight (del x lt) = bheight lt \<and> invc (del x lt) 
  \<or> color lt = Black \<and> bheight (del x lt) = bheight lt - 1 \<and> invc2 (del x lt))"
and  "\<lbrakk>invh rt; bheight lt = bheight rt; invc rt\<rbrakk> \<Longrightarrow>
   invh (delL x lt k rt) \<and> 
   bheight (delL x lt k rt) = bheight lt \<and> 
   (color lt = Black \<and> color rt = Black \<and> invc (delL x lt k rt) \<or> 
    (color lt \<noteq> Black \<or> color rt \<noteq> Black) \<and> invc2 (delL x lt k rt))"
  and "\<lbrakk>invh rt; bheight lt = bheight rt; invc rt\<rbrakk> \<Longrightarrow>
  invh (delR x lt k rt) \<and> 
  bheight (delR x lt k rt) = bheight lt \<and> 
  (color lt = Black \<and> color rt = Black \<and> invc (delR x lt k rt) \<or> 
   (color lt \<noteq> Black \<or> color rt \<noteq> Black) \<and> invc2 (delR x lt k rt))"
using assms
proof (induct x lt and x lt k rt and x lt k rt rule: del_delL_delR.induct)
case (2 y c _ y')
  have "y = y' \<or> y < y' \<or> y > y'" by auto
  thus ?case proof (elim disjE)
    assume "y = y'"
    with 2 show ?thesis
    by (cases c) (simp_all add: invh_combine invc_combine)
  next
    assume "y < y'"
    with 2 show ?thesis by (cases c) (auto simp: invc2I)
  next
    assume "y' < y"
    with 2 show ?thesis by (cases c) (auto simp: invc2I)
  qed
next
  case (3 y lt z rta y' bb)
  thus ?case by (cases "color (Node Black lt z rta) = Black \<and> color bb = Black") (simp add: balL_invh_with_invc balL_invc balL_invc2)+
next
  case (5 y a y' lt z rta)
  thus ?case by (cases "color a = Black \<and> color (Node Black lt z rta) = Black") (simp add: balR_invh_with_invc invc_balR invc2_balR)+
next
  case ("6_1" y a y') thus ?case by (cases "color a = Black \<and> color Leaf = Black") simp+
qed auto

theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete k t)"
by (metis delete_def rbt_def color_paint_Black del_invc_invh invc_paint_Black invc2I invh_paint)

text \<open>Overall correctness:\<close>

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = rbt
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp add: rbt_Leaf) 
next
  case 6 thus ?case by (simp add: rbt_insert) 
next
  case 7 thus ?case by (simp add: rbt_delete) 
qed


subsection \<open>Height-Size Relation\<close>

lemma neq_Black[simp]: "(c \<noteq> Black) = (c = Red)"
by (cases c) auto

lemma rbt_height_bheight_if_nat: "invc t \<Longrightarrow> invh t \<Longrightarrow>
  height t \<le> (if color t = Black then 2 * bheight t else 2 * bheight t + 1)"
by(induction t) (auto split: if_split_asm)

lemma rbt_height_bheight_if: "invc t \<Longrightarrow> invh t \<Longrightarrow>
  (if color t = Black then height t / 2 else (height t - 1) / 2) \<le> bheight t"
by(induction t) (auto split: if_split_asm)

lemma rbt_height_bheight: "rbt t \<Longrightarrow> height t / 2 \<le> bheight t "
by(auto simp: rbt_def dest: rbt_height_bheight_if)

lemma bheight_size_bound:  "invc t \<Longrightarrow> invh t \<Longrightarrow> size1 t \<ge>  2 ^ (bheight t)"
by (induction t) auto

lemma rbt_height_le: assumes "rbt t" shows "height t \<le> 2 * log 2 (size1 t)"
proof -
  have "2 powr (height t / 2) \<le> 2 powr bheight t"
    using rbt_height_bheight[OF assms] by (simp)
  also have "\<dots> \<le> size1 t" using assms
    by (simp add: powr_realpow bheight_size_bound rbt_def)
  finally have "2 powr (height t / 2) \<le> size1 t" .
  hence "height t / 2 \<le> log 2 (size1 t)"
    by(simp add: le_log_iff size1_def del: Int.divide_le_eq_numeral1(1))
  thus ?thesis by simp
qed

end
