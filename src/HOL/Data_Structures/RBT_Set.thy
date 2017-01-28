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
     LT \<Rightarrow> baliL (ins x l) a r |
     GT \<Rightarrow> baliR l a (ins x r) |
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
"delL x (B t1 a t2) b t3 = baldL (del x (B t1 a t2)) b t3" |
"delL x l a r = R (del x l) a r" |
"delR x t1 a (B t2 b t3) = baldR t1 a (del x (B t2 b t3))" | 
"delR x l a r = R l a (del x r)"

definition delete :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

lemma inorder_paint: "inorder(paint c t) = inorder t"
by(cases t) (auto)

lemma inorder_baliL:
  "inorder(baliL l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baliL.cases) (auto)

lemma inorder_baliR:
  "inorder(baliR l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baliR.cases) (auto)

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(ins x t) = ins_list x (inorder t)"
by(induction x t rule: ins.induct)
  (auto simp: ins_list_simps inorder_baliL inorder_baliR)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (simp add: insert_def inorder_ins inorder_paint)

lemma inorder_baldL:
  "inorder(baldL l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baldL.cases)
  (auto simp:  inorder_baliL inorder_baliR inorder_paint)

lemma inorder_baldR:
  "inorder(baldR l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baldR.cases)
  (auto simp:  inorder_baliL inorder_baliR inorder_paint)

lemma inorder_combine:
  "inorder(combine l r) = inorder l @ inorder r"
by(induction l r rule: combine.induct)
  (auto simp: inorder_baldL inorder_baldR split: tree.split color.split)

lemma inorder_del:
 "sorted(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
 "sorted(inorder l) \<Longrightarrow>  inorder(delL x l a r) =
    del_list x (inorder l) @ a # inorder r"
 "sorted(inorder r) \<Longrightarrow>  inorder(delR x l a r) =
    inorder l @ a # del_list x (inorder r)"
by(induction x t and x l a r and x l a r rule: del_delL_delR.induct)
  (auto simp: del_list_simps inorder_combine inorder_baldL inorder_baldR)

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

lemma invc_baliL:
  "\<lbrakk>invc2 l; invc r\<rbrakk> \<Longrightarrow> invc (baliL l a r)" 
by (induct l a r rule: baliL.induct) auto

lemma invc_baliR:
  "\<lbrakk>invc l; invc2 r\<rbrakk> \<Longrightarrow> invc (baliR l a r)" 
by (induct l a r rule: baliR.induct) auto

lemma bheight_baliL:
  "bheight l = bheight r \<Longrightarrow> bheight (baliL l a r) = Suc (bheight l)"
by (induct l a r rule: baliL.induct) auto

lemma bheight_baliR:
  "bheight l = bheight r \<Longrightarrow> bheight (baliR l a r) = Suc (bheight l)"
by (induct l a r rule: baliR.induct) auto

lemma invh_baliL: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliL l a r)"
by (induct l a r rule: baliL.induct) auto

lemma invh_baliR: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliR l a r)"
by (induct l a r rule: baliR.induct) auto


subsubsection \<open>Insertion\<close>

lemma invc_ins: assumes "invc t"
  shows "color t = Black \<Longrightarrow> invc (ins x t)" "invc2 (ins x t)"
using assms
by (induct x t rule: ins.induct) (auto simp: invc_baliL invc_baliR invc2I)

lemma invh_ins: assumes "invh t"
  shows "invh (ins x t)" "bheight (ins x t) = bheight t"
using assms
by(induct x t rule: ins.induct)
  (auto simp: invh_baliL invh_baliR bheight_baliL bheight_baliR)

theorem rbt_insert: "rbt t \<Longrightarrow> rbt (insert x t)"
by (simp add: invc_ins invh_ins color_paint_Black invc_paint_Black invh_paint
  rbt_def insert_def)


subsubsection \<open>Deletion\<close>

lemma bheight_paint_Red:
  "color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
by (cases t) auto

lemma baldL_invh_with_invc:
  assumes "invh l" "invh r" "bheight l + 1 = bheight r" "invc r"
  shows "bheight (baldL l a r) = bheight l + 1"  "invh (baldL l a r)"
using assms 
by (induct l a r rule: baldL.induct)
   (auto simp: invh_baliR invh_paint bheight_baliR bheight_paint_Red)

lemma baldL_invh_app: 
  assumes "invh l" "invh r" "bheight l + 1 = bheight r" "color r = Black"
  shows "invh (baldL l a r)" 
        "bheight (baldL l a r) = bheight r"
using assms 
by (induct l a r rule: baldL.induct) (auto simp add: invh_baliR bheight_baliR) 

lemma baldL_invc: "\<lbrakk>invc2 l; invc r; color r = Black\<rbrakk> \<Longrightarrow> invc (baldL l a r)"
by (induct l a r rule: baldL.induct) (simp_all add: invc_baliR)

lemma baldL_invc2: "\<lbrakk> invc2 l; invc r \<rbrakk> \<Longrightarrow> invc2 (baldL l a r)"
by (induct l a r rule: baldL.induct) (auto simp: invc_baliR paint_invc2 invc2I)

lemma baldR_invh_with_invc:
  assumes "invh l" "invh r" "bheight l = bheight r + 1" "invc l"
  shows "invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l"
using assms
by(induct l a r rule: baldR.induct)
  (auto simp: invh_baliL bheight_baliL invh_paint bheight_paint_Red)

lemma invc_baldR: "\<lbrakk>invc a; invc2 b; color a = Black\<rbrakk> \<Longrightarrow> invc (baldR a x b)"
by (induct a x b rule: baldR.induct) (simp_all add: invc_baliL)

lemma invc2_baldR: "\<lbrakk> invc l; invc2 r \<rbrakk> \<Longrightarrow>invc2 (baldR l x r)"
by (induct l x r rule: baldR.induct) (auto simp: invc_baliL paint_invc2 invc2I)

lemma invh_combine:
  assumes "invh l" "invh r" "bheight l = bheight r"
  shows "bheight (combine l r) = bheight l" "invh (combine l r)"
using assms 
by (induct l r rule: combine.induct) 
   (auto simp: baldL_invh_app split: tree.splits color.splits)

lemma invc_combine: 
  assumes "invc l" "invc r"
  shows "color l = Black \<Longrightarrow> color r = Black \<Longrightarrow> invc (combine l r)"
         "invc2 (combine l r)"
using assms 
by (induct l r rule: combine.induct)
   (auto simp: baldL_invc invc2I split: tree.splits color.splits)


lemma assumes "invh l" "invc l"
  shows del_invc_invh:
   "invh (del x l) \<and>
   (color l = Red \<and> bheight (del x l) = bheight l \<and> invc (del x l) \<or>
    color l = Black \<and> bheight (del x l) = bheight l - 1 \<and> invc2 (del x l))"
and  "\<lbrakk>invh r; bheight l = bheight r; invc r\<rbrakk> \<Longrightarrow>
   invh (delL x l k r) \<and> 
   bheight (delL x l k r) = bheight l \<and> 
   (color l = Black \<and> color r = Black \<and> invc (delL x l k r) \<or> 
    (color l \<noteq> Black \<or> color r \<noteq> Black) \<and> invc2 (delL x l k r))"
  and "\<lbrakk>invh r; bheight l = bheight r; invc r\<rbrakk> \<Longrightarrow>
  invh (delR x l k r) \<and> 
  bheight (delR x l k r) = bheight l \<and> 
  (color l = Black \<and> color r = Black \<and> invc (delR x l k r) \<or> 
   (color l \<noteq> Black \<or> color r \<noteq> Black) \<and> invc2 (delR x l k r))"
using assms
proof (induct x l and x l k r and x l k r rule: del_delL_delR.induct)
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
  case (3 y l z ra y' bb)
  thus ?case by (cases "color (Node Black l z ra) = Black \<and> color bb = Black") (simp add: baldL_invh_with_invc baldL_invc baldL_invc2)+
next
  case (5 y a y' l z ra)
  thus ?case by (cases "color a = Black \<and> color (Node Black l z ra) = Black") (simp add: baldR_invh_with_invc invc_baldR invc2_baldR)+
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
