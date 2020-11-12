(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Sets\<close>

theory RBT_Set
imports
  Complex_Main
  RBT
  Cmp
  Isin2
begin

definition empty :: "'a rbt" where
"empty = Leaf"

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

fun color :: "'a rbt \<Rightarrow> color" where
"color Leaf = Black" |
"color (Node _ (_, c) _) = c"

fun del :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"del x Leaf = Leaf" |
"del x (Node l (a, _) r) =
  (case cmp x a of
     LT \<Rightarrow> if l \<noteq> Leaf \<and> color l = Black
           then baldL (del x l) a r else R (del x l) a r |
     GT \<Rightarrow> if r \<noteq> Leaf\<and> color r = Black
           then baldR l a (del x r) else R l a (del x r) |
     EQ \<Rightarrow> join l r)"

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

lemma inorder_join:
  "inorder(join l r) = inorder l @ inorder r"
by(induction l r rule: join.induct)
  (auto simp: inorder_baldL inorder_baldR split: tree.split color.split)

lemma inorder_del:
 "sorted(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
by(induction x t rule: del.induct)
  (auto simp: del_list_simps inorder_join inorder_baldL inorder_baldR)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by (auto simp: delete_def inorder_del inorder_paint)


subsection \<open>Structural invariants\<close>

lemma neq_Black[simp]: "(c \<noteq> Black) = (c = Red)"
by (cases c) auto

text\<open>The proofs are due to Markus Reiter and Alexander Krauss.\<close>

fun bheight :: "'a rbt \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node l (x, c) r) = (if c = Black then bheight l + 1 else bheight l)"

fun invc :: "'a rbt \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node l (a,c) r) =
  ((c = Red \<longrightarrow> color l = Black \<and> color r = Black) \<and> invc l \<and> invc r)"

text \<open>Weaker version:\<close>
abbreviation invc2 :: "'a rbt \<Rightarrow> bool" where
"invc2 t \<equiv> invc(paint Black t)"

fun invh :: "'a rbt \<Rightarrow> bool" where
"invh Leaf = True" |
"invh (Node l (x, c) r) = (bheight l = bheight r \<and> invh l \<and> invh r)"

lemma invc2I: "invc t \<Longrightarrow> invc2 t"
by (cases t rule: tree2_cases) simp+

definition rbt :: "'a rbt \<Rightarrow> bool" where
"rbt t = (invc t \<and> invh t \<and> color t = Black)"

lemma color_paint_Black: "color (paint Black t) = Black"
by (cases t) auto

lemma paint2: "paint c2 (paint c1 t) = paint c2 t"
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

text \<open>All in one:\<close>

lemma inv_baliR: "\<lbrakk> invh l; invh r; invc l; invc2 r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> invc (baliR l a r) \<and> invh (baliR l a r) \<and> bheight (baliR l a r) = Suc (bheight l)"
by (induct l a r rule: baliR.induct) auto

lemma inv_baliL: "\<lbrakk> invh l; invh r; invc2 l; invc r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> invc (baliL l a r) \<and> invh (baliL l a r) \<and> bheight (baliL l a r) = Suc (bheight l)"
by (induct l a r rule: baliL.induct) auto

subsubsection \<open>Insertion\<close>

lemma invc_ins: "invc t \<longrightarrow> invc2 (ins x t) \<and> (color t = Black \<longrightarrow> invc (ins x t))"
by (induct x t rule: ins.induct) (auto simp: invc_baliL invc_baliR invc2I)

lemma invh_ins: "invh t \<Longrightarrow> invh (ins x t) \<and> bheight (ins x t) = bheight t"
by(induct x t rule: ins.induct)
  (auto simp: invh_baliL invh_baliR bheight_baliL bheight_baliR)

theorem rbt_insert: "rbt t \<Longrightarrow> rbt (insert x t)"
by (simp add: invc_ins invh_ins color_paint_Black invh_paint rbt_def insert_def)

text \<open>All in one:\<close>

lemma inv_ins: "\<lbrakk> invc t; invh t \<rbrakk> \<Longrightarrow>
  invc2 (ins x t) \<and> (color t = Black \<longrightarrow> invc (ins x t)) \<and>
  invh(ins x t) \<and> bheight (ins x t) = bheight t"
by (induct x t rule: ins.induct) (auto simp: inv_baliL inv_baliR invc2I)

theorem rbt_insert2: "rbt t \<Longrightarrow> rbt (insert x t)"
by (simp add: inv_ins color_paint_Black invh_paint rbt_def insert_def)


subsubsection \<open>Deletion\<close>

lemma bheight_paint_Red:
  "color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
by (cases t) auto

lemma invh_baldL_invc:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  invc r \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
by (induct l a r rule: baldL.induct)
   (auto simp: invh_baliR invh_paint bheight_baliR bheight_paint_Red)

lemma invh_baldL_Black: 
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  color r = Black \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
by (induct l a r rule: baldL.induct) (auto simp add: invh_baliR bheight_baliR) 

lemma invc_baldL: "\<lbrakk>invc2 l; invc r; color r = Black\<rbrakk> \<Longrightarrow> invc (baldL l a r)"
by (induct l a r rule: baldL.induct) (simp_all add: invc_baliR)

lemma invc2_baldL: "\<lbrakk> invc2 l; invc r \<rbrakk> \<Longrightarrow> invc2 (baldL l a r)"
by (induct l a r rule: baldL.induct) (auto simp: invc_baliR paint2 invc2I)

lemma invh_baldR_invc:
  "\<lbrakk> invh l;  invh r;  bheight l = bheight r + 1;  invc l \<rbrakk>
  \<Longrightarrow> invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l"
by(induct l a r rule: baldR.induct)
  (auto simp: invh_baliL bheight_baliL invh_paint bheight_paint_Red)

lemma invc_baldR: "\<lbrakk>invc l; invc2 r; color l = Black\<rbrakk> \<Longrightarrow> invc (baldR l a r)"
by (induct l a r rule: baldR.induct) (simp_all add: invc_baliL)

lemma invc2_baldR: "\<lbrakk> invc l; invc2 r \<rbrakk> \<Longrightarrow>invc2 (baldR l a r)"
by (induct l a r rule: baldR.induct) (auto simp: invc_baliL paint2 invc2I)

lemma invh_join:
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk>
  \<Longrightarrow> invh (join l r) \<and> bheight (join l r) = bheight l"
by (induct l r rule: join.induct) 
   (auto simp: invh_baldL_Black split: tree.splits color.splits)

lemma invc_join: 
  "\<lbrakk> invc l; invc r \<rbrakk> \<Longrightarrow>
  (color l = Black \<and> color r = Black \<longrightarrow> invc (join l r)) \<and> invc2 (join l r)"
by (induct l r rule: join.induct)
   (auto simp: invc_baldL invc2I split: tree.splits color.splits)

text \<open>All in one:\<close>

lemma inv_baldL:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r; invc2 l; invc r \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r
  \<and> invc2 (baldL l a r) \<and> (color r = Black \<longrightarrow> invc (baldL l a r))"
by (induct l a r rule: baldL.induct)
   (auto simp: inv_baliR invh_paint bheight_baliR bheight_paint_Red paint2 invc2I)

lemma inv_baldR:
  "\<lbrakk> invh l;  invh r;  bheight l = bheight r + 1; invc l; invc2 r \<rbrakk>
   \<Longrightarrow> invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l
  \<and> invc2 (baldR l a r) \<and> (color l = Black \<longrightarrow> invc (baldR l a r))"
by (induct l a r rule: baldR.induct)
   (auto simp: inv_baliL invh_paint bheight_baliL bheight_paint_Red paint2 invc2I)

lemma inv_join:
  "\<lbrakk> invh l; invh r; bheight l = bheight r; invc l; invc r \<rbrakk>
  \<Longrightarrow> invh (join l r) \<and> bheight (join l r) = bheight l
  \<and> invc2 (join l r) \<and> (color l = Black \<and> color r = Black \<longrightarrow> invc (join l r))"
by (induct l r rule: join.induct) 
   (auto simp: invh_baldL_Black inv_baldL invc2I split: tree.splits color.splits)

lemma neq_LeafD: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x c r. t = Node l (x,c) r"
by(cases t rule: tree2_cases) auto

lemma inv_del: "\<lbrakk> invh t; invc t \<rbrakk> \<Longrightarrow>
   invh (del x t) \<and>
   (color t = Red \<and> bheight (del x t) = bheight t \<and> invc (del x t) \<or>
    color t = Black \<and> bheight (del x t) = bheight t - 1 \<and> invc2 (del x t))"
by(induct x t rule: del.induct)
  (auto simp: inv_baldL inv_baldR inv_join dest!: neq_LeafD)

theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete x t)"
by (metis delete_def rbt_def color_paint_Black inv_del invc2I invh_paint)

text \<open>Overall correctness:\<close>

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = rbt
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: isin_set_inorder)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp add: rbt_def empty_def) 
next
  case 6 thus ?case by (simp add: rbt_insert) 
next
  case 7 thus ?case by (simp add: rbt_delete) 
qed


subsection \<open>Height-Size Relation\<close>

lemma rbt_height_bheight_if: "invc t \<Longrightarrow> invh t \<Longrightarrow>
  height t \<le> 2 * bheight t + (if color t = Black then 0 else 1)"
by(induction t) (auto split: if_split_asm)

lemma rbt_height_bheight: "rbt t \<Longrightarrow> height t / 2 \<le> bheight t "
by(auto simp: rbt_def dest: rbt_height_bheight_if)

lemma bheight_size_bound:  "invc t \<Longrightarrow> invh t \<Longrightarrow> 2 ^ (bheight t) \<le> size1 t"
by (induction t) auto

lemma rbt_height_le: assumes "rbt t" shows "height t \<le> 2 * log 2 (size1 t)"
proof -
  have "2 powr (height t / 2) \<le> 2 powr bheight t"
    using rbt_height_bheight[OF assms] by (simp)
  also have "\<dots> \<le> size1 t" using assms
    by (simp add: powr_realpow bheight_size_bound rbt_def)
  finally have "2 powr (height t / 2) \<le> size1 t" .
  hence "height t / 2 \<le> log 2 (size1 t)"
    by (simp add: le_log_iff size1_size del: divide_le_eq_numeral1(1))
  thus ?thesis by simp
qed

end
