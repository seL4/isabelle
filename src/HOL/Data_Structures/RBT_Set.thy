(* Author: Tobias Nipkow, Daniel Stüwe *)

section \<open>Red-Black Tree Implementation of Sets\<close>

theory RBT_Set
imports
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

text\<open>The proofs are due to Markus Reiter and Alexander Krauss,\<close>

fun color :: "'a rbt \<Rightarrow> color" where
"color Leaf = Black" |
"color (Node c _ _ _) = c"

fun bheight :: "'a rbt \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node c l x r) = (if c = Black then Suc(bheight l) else bheight l)"

fun invc :: "'a rbt \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node c l a r) =
  (invc l \<and> invc r \<and> (c = Black \<or> color l = Black \<and> color r = Black))"

fun invc_sons :: "'a rbt \<Rightarrow> bool" \<comment> \<open>Weaker version\<close> where
"invc_sons Leaf = True" |
"invc_sons (Node c l a r) = (invc l \<and> invc r)"

fun invh :: "'a rbt \<Rightarrow> bool" where
"invh Leaf = True" |
"invh (Node c l x r) = (invh l \<and> invh r \<and> bheight l = bheight r)"

lemma invc_sonsI: "invc t \<Longrightarrow> invc_sons t"
by (cases t) simp+

definition rbt :: "'a rbt \<Rightarrow> bool" where
"rbt t = (invc t \<and> invh t \<and> color t = Black)"

lemma color_paint_Black: "color (paint Black t) = Black"
by (cases t) auto

theorem rbt_Leaf: "rbt Leaf"
by (simp add: rbt_def)

lemma paint_invc_sons: "invc_sons t \<Longrightarrow> invc_sons (paint c t)"
by (cases t) auto

lemma invc_paint_Black: "invc_sons t \<Longrightarrow> invc (paint Black t)"
by (cases t) auto

lemma invh_paint: "invh t \<Longrightarrow> invh (paint c t)"
by (cases t) auto

lemma invc_bal: "\<lbrakk>invc_sons l; invc_sons r\<rbrakk> \<Longrightarrow> invc (bal l a r)" 
by (induct l a r rule: bal.induct) auto

lemma bheight_bal:
  "bheight l = bheight r \<Longrightarrow> bheight (bal l a r) = Suc (bheight l)"
by (induct l a r rule: bal.induct) auto

lemma invh_bal: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (bal l a r)"
by (induct l a r rule: bal.induct) auto


subsubsection \<open>Insertion\<close>

lemma invc_ins: assumes "invc t"
  shows "color t = Black \<Longrightarrow> invc (ins x t)" "invc_sons (ins x t)"
using assms
by (induct x t rule: ins.induct) (auto simp: invc_bal invc_sonsI)

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

lemma balL_invc: "\<lbrakk>invc_sons l; invc r; color r = Black\<rbrakk> \<Longrightarrow> invc (balL l a r)"
by (induct l a r rule: balL.induct) (simp_all add: invc_bal)

lemma balL_invc_sons: "\<lbrakk> invc_sons lt; invc rt \<rbrakk> \<Longrightarrow> invc_sons (balL lt a rt)"
by (induct lt a rt rule: balL.induct) (auto simp: invc_bal paint_invc_sons invc_sonsI)

lemma balR_invh_with_invc:
  assumes "invh lt" "invh rt" "bheight lt = bheight rt + 1" "invc lt"
  shows "invh (balR lt a rt) \<and> bheight (balR lt a rt) = bheight lt"
using assms
by(induct lt a rt rule: balR.induct)
  (auto simp: invh_bal bheight_bal invh_paint bheight_paint_Red)

lemma invc_balR: "\<lbrakk>invc a; invc_sons b; color a = Black\<rbrakk> \<Longrightarrow> invc (balR a x b)"
by (induct a x b rule: balR.induct) (simp_all add: invc_bal)

lemma invc_sons_balR: "\<lbrakk> invc lt; invc_sons rt \<rbrakk> \<Longrightarrow>invc_sons (balR lt x rt)"
by (induct lt x rt rule: balR.induct) (auto simp: invc_bal paint_invc_sons invc_sonsI)

lemma invh_combine:
  assumes "invh lt" "invh rt" "bheight lt = bheight rt"
  shows "bheight (combine lt rt) = bheight lt" "invh (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct) 
   (auto simp: balL_invh_app split: tree.splits color.splits)

lemma invc_combine: 
  assumes "invc lt" "invc rt"
  shows "color lt = Black \<Longrightarrow> color rt = Black \<Longrightarrow> invc (combine lt rt)"
         "invc_sons (combine lt rt)"
using assms 
by (induct lt rt rule: combine.induct)
   (auto simp: balL_invc invc_sonsI split: tree.splits color.splits)


lemma assumes "invh lt" "invc lt"
  shows
  del_invc_invh: "invh (del x lt) \<and> (color lt = Red \<and> bheight (del x lt) = bheight lt \<and> invc (del x lt) 
  \<or> color lt = Black \<and> bheight (del x lt) = bheight lt - 1 \<and> invc_sons (del x lt))"
and  "\<lbrakk>invh rt; bheight lt = bheight rt; invc rt\<rbrakk> \<Longrightarrow>
   invh (delL x lt k rt) \<and> 
   bheight (delL x lt k rt) = bheight lt \<and> 
   (color lt = Black \<and> color rt = Black \<and> invc (delL x lt k rt) \<or> 
    (color lt \<noteq> Black \<or> color rt \<noteq> Black) \<and> invc_sons (delL x lt k rt))"
  and "\<lbrakk>invh rt; bheight lt = bheight rt; invc rt\<rbrakk> \<Longrightarrow>
  invh (delR x lt k rt) \<and> 
  bheight (delR x lt k rt) = bheight lt \<and> 
  (color lt = Black \<and> color rt = Black \<and> invc (delR x lt k rt) \<or> 
   (color lt \<noteq> Black \<or> color rt \<noteq> Black) \<and> invc_sons (delR x lt k rt))"
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
    with 2 show ?thesis by (cases c) (auto simp: invc_sonsI)
  next
    assume "y' < y"
    with 2 show ?thesis by (cases c) (auto simp: invc_sonsI)
  qed
next
  case (3 y lt z rta y' bb)
  thus ?case by (cases "color (Node Black lt z rta) = Black \<and> color bb = Black") (simp add: balL_invh_with_invc balL_invc balL_invc_sons)+
next
  case (5 y a y' lt z rta)
  thus ?case by (cases "color a = Black \<and> color (Node Black lt z rta) = Black") (simp add: balR_invh_with_invc invc_balR invc_sons_balR)+
next
  case ("6_1" y a y') thus ?case by (cases "color a = Black \<and> color Leaf = Black") simp+
qed auto

theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete k t)"
by (metis delete_def rbt_def color_paint_Black del_invc_invh invc_paint_Black invc_sonsI invh_paint)

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

text \<open>By Daniel St\"uwe\<close>

lemma color_RedE:"color t = Red \<Longrightarrow> invc t =
 (\<exists> l a r . t = R l a r \<and> color l = Black \<and> color r = Black \<and> invc l \<and> invc r)"
by (cases t) auto

lemma rbt_induct[consumes 1]:
  assumes "rbt t"
  assumes [simp]: "P Leaf"
  assumes "\<And> t l a r. \<lbrakk>t = B l a r; invc t; invh t; Q(l); Q(r)\<rbrakk> \<Longrightarrow> P t"
  assumes "\<And> t l a r. \<lbrakk>t = R l a r; invc t; invh t; P(l); P(r)\<rbrakk> \<Longrightarrow> Q t"
  assumes "\<And> t . P(t) \<Longrightarrow> Q(t)"
  shows "P t"
using assms(1) unfolding rbt_def apply safe
proof (induction t rule: measure_induct[of size])
case (1 t)
  note * = 1 assms
  show ?case proof (cases t)
    case [simp]: (Node c l a r)
    show ?thesis proof (cases c)
      case Red thus ?thesis using 1 by simp
    next
      case [simp]: Black
      show ?thesis
      proof (cases "color l")
        case Red
        thus ?thesis using * by (cases "color r") (auto simp: color_RedE)
      next
        case Black
        thus ?thesis using * by (cases "color r") (auto simp: color_RedE)
      qed
    qed
  qed simp
qed

lemma rbt_b_height: "rbt t \<Longrightarrow> bheight t * 2 \<ge> height t"
by (induction t rule: rbt_induct[where Q="\<lambda> t. bheight t * 2 + 1 \<ge> height t"]) auto

lemma red_b_height: "invc t \<Longrightarrow> invh t \<Longrightarrow> bheight t * 2 + 1 \<ge> height t"
apply (cases t) apply simp
  using rbt_b_height unfolding rbt_def
  by (cases "color t") fastforce+

lemma red_b_height2: "invc t \<Longrightarrow> invh t \<Longrightarrow> bheight t \<ge> height t div 2"
using red_b_height by fastforce

lemma rbt_b_height2: "bheight t \<le> height t"
by (induction t) auto

lemma "rbt t \<Longrightarrow> size1 t \<le>  4 ^ (bheight t)"
by(induction t rule: rbt_induct[where Q="\<lambda> t. size1 t \<le>  2 * 4 ^ (bheight t)"]) auto

lemma bheight_size_bound:  "rbt t \<Longrightarrow> size1 t \<ge>  2 ^ (bheight t)"
by (induction t rule: rbt_induct[where Q="\<lambda> t. size1 t \<ge>  2 ^ (bheight t)"]) auto

text \<open>Balanced red-balck tree with all black nodes:\<close>
inductive balB :: "nat \<Rightarrow> unit rbt \<Rightarrow> bool"  where
"balB 0 Leaf" |
"balB h t \<Longrightarrow> balB (Suc h) (B t () t)"

inductive_cases [elim!]: "balB 0 t"
inductive_cases [elim]: "balB (Suc h) t"

lemma balB_hs: "balB h t \<Longrightarrow> bheight t = height t"
by (induction h t rule: "balB.induct") auto

lemma balB_h: "balB h t \<Longrightarrow> h = height t"
by (induction h t rule: "balB.induct") auto

lemma "rbt t \<Longrightarrow> balB (bheight t) t' \<Longrightarrow> size t' \<le> size t"
by (induction t arbitrary: t' 
 rule: rbt_induct[where Q="\<lambda> t . \<forall> h t'. balB (bheight t) t' \<longrightarrow> size t' \<le> size t"])
 fastforce+

lemma balB_bh: "invc t \<Longrightarrow> invh t \<Longrightarrow> balB (bheight t) t' \<Longrightarrow> size t' \<le> size t"
by (induction t arbitrary: t') (fastforce split: if_split_asm)+

lemma balB_bh3:"\<lbrakk> balB h t; balB (h' + h) t' \<rbrakk> \<Longrightarrow> size t \<le> size t'"
by (induction h t arbitrary: t' h' rule: balB.induct)  fastforce+

corollary balB_bh3': "\<lbrakk> balB h t; balB h' t'; h \<le> h' \<rbrakk> \<Longrightarrow> size t \<le> size t'"
using balB_bh3 le_Suc_ex by (fastforce simp: algebra_simps)

lemma exist_pt: "\<exists> t . balB h t"
by (induction h) (auto intro: balB.intros)

corollary compact_pt:
  assumes "invc t" "invh t" "h \<le> bheight t" "balB h t'"
  shows   "size t' \<le> size t"
proof -
  obtain t'' where "balB (bheight t) t''" using exist_pt by blast
  thus ?thesis using assms balB_bh[of t t''] balB_bh3'[of h t' "bheight t" t''] by auto
qed

lemma balB_bh2: "balB (bheight t) t'\<Longrightarrow> invc t \<Longrightarrow> invh t \<Longrightarrow> height t' \<le> height t"
apply (induction "(bheight t)" t' arbitrary: t rule: balB.induct)
using balB_h rbt_b_height2 by auto

lemma balB_rbt: "balB h t \<Longrightarrow> rbt t"
unfolding rbt_def
by (induction h t rule: balB.induct) auto

lemma balB_size[simp]: "balB h t \<Longrightarrow> size1 t = 2^h"
by (induction h t rule: balB.induct) auto

text \<open>Red-black tree (except that the root may be red) of minimal size
for a given height:\<close>

inductive RB :: "nat \<Rightarrow> unit rbt \<Rightarrow> bool" where
"RB 0 Leaf" |
"balB (h div 2) t \<Longrightarrow> RB h t' \<Longrightarrow> color t' = Red \<Longrightarrow> RB (Suc h) (B t' () t)" |
"balB (h div 2) t \<Longrightarrow> RB h t' \<Longrightarrow> color t' = Black \<Longrightarrow> RB (Suc h) (R t' () t)" 

lemmas RB.intros[intro]

lemma RB_invc: "RB h t \<Longrightarrow> invc t"
apply (induction h t rule: RB.induct)
using balB_rbt unfolding rbt_def by auto

lemma RB_h: "RB h t \<Longrightarrow> h = height t"
apply (induction h t rule: RB.induct)
using balB_h by auto

lemma RB_mod: "RB h t \<Longrightarrow> (color t = Black \<longleftrightarrow> h mod 2 = 0)"
apply (induction h t rule: RB.induct)
apply auto
by presburger

lemma RB_b_height: "RB h t \<Longrightarrow> height t div 2 = bheight t"
proof  (induction h t rule: RB.induct)
  case 1 
  thus ?case by auto 
next
  case (2 h t t')
  with RB_mod obtain n where "2*n + 1 = h" 
    by (metis color.distinct(1) mult_div_mod_eq parity) 
  with 2 balB_h RB_h show ?case by auto
next
  case (3 h t t')
  with RB_mod[OF 3(2)] parity obtain n where "2*n = h" by blast
  with 3 balB_h RB_h show ?case by auto
qed

lemma weak_RB_induct[consumes 1]: 
  "RB h t \<Longrightarrow> P 0 \<langle>\<rangle> \<Longrightarrow> (\<And>h t t' c . balB (h div 2) t \<Longrightarrow> RB h t' \<Longrightarrow>
    P h t' \<Longrightarrow> P (Suc h) (Node c t' () t)) \<Longrightarrow> P h t"
using RB.induct by metis

lemma RB_invh: "RB h t \<Longrightarrow> invh t"
apply (induction h t rule: weak_RB_induct)
  using balB_h balB_hs RB_h balB_rbt RB_b_height
  unfolding rbt_def
by auto

lemma RB_bheight_minimal:
  "\<lbrakk>RB (height t') t; invc t'; invh t'\<rbrakk> \<Longrightarrow> bheight t \<le> bheight t'"
using RB_b_height RB_h red_b_height2 by fastforce

lemma RB_minimal: "RB (height t') t \<Longrightarrow> invh t \<Longrightarrow> invc t' \<Longrightarrow> invh t' \<Longrightarrow> size t \<le> size t'"
proof (induction "(height t')" t arbitrary: t' rule: weak_RB_induct)
  case 1 thus ?case by auto 
next
  case (2 h t t'')
  have ***: "size (Node c t'' () t) \<le> size t'"
    if assms:
      "\<And> (t' :: 'a rbt) . \<lbrakk> h = height t'; invh t''; invc t'; invh t' \<rbrakk>
                            \<Longrightarrow> size t'' \<le> size t'"
      "Suc h = height t'" "balB (h div 2) t" "RB h t''"
      "invc t'" "invh t'" "height l \<ge> height r"
      and tt[simp]:"t' = Node c l a r" and last: "invh (Node c t'' () t)"
  for t' :: "'a rbt" and c l a r
  proof -
    from assms have inv: "invc r" "invh r" by auto
    from assms have "height l = h" using max_def by auto
    with RB_bheight_minimal[of l t''] have
      "bheight t \<le> bheight r" using assms last by auto
    with compact_pt[OF inv] balB_h balB_hs have 
      "size t \<le> size r" using assms(3) by auto moreover
    have "size t'' \<le> size l" using assms last by auto ultimately
    show ?thesis by simp
  qed
  
  from 2 obtain c l a r where 
    t': "t' = Node c l a r" by (cases t') auto
  with 2 have inv: "invc l" "invh l" "invc r" "invh r" by auto
  show ?case proof (cases "height r \<le> height l")
    case True thus ?thesis using ***[OF 2(3,4,1,2,6,7)] t' 2(5) by auto
  next
    case False 
    obtain t''' where t''' : "t''' = Node c r a l" "invc t'''" "invh t'''" using 2 t' by auto
    have "size t''' = size t'" and 4 : "Suc h = height t'''" using 2(4) t' t''' by auto
    thus ?thesis using ***[OF 2(3) 4 2(1,2) t'''(2,3) _ t'''(1)] 2(5) False by auto
  qed
qed

lemma RB_size: "RB h t \<Longrightarrow> size1 t + 1 = 2^((h+1) div 2) + 2^(h div 2)"
by (induction h t rule: "RB.induct" ) auto

lemma RB_exist: "\<exists> t . RB h t"
proof (induction h) 
  case (Suc n)
  obtain r where r: "balB (n div 2) r"  using  exist_pt by blast
  obtain l where l: "RB n l"  using  Suc by blast
  obtain t where 
    "color l = Red   \<Longrightarrow> t = B l () r"
    "color l = Black \<Longrightarrow> t = R l () r" by auto
  with l and r have "RB (Suc n) t" by (cases "color l") auto
  thus ?case by auto
qed auto

lemma bound:
  assumes "invc t"  "invh t" and [simp]:"height t = h"
  shows "size t \<ge> 2^((h+1) div 2) + 2^(h div 2) - 2"
proof -
  obtain t' where t': "RB h t'" using RB_exist by auto
  show ?thesis using RB_size[OF t'] 
  RB_minimal[OF _ _ assms(1,2), simplified, OF t' RB_invh[OF t']] assms t' 
  unfolding  size1_def by auto
qed

corollary "rbt t \<Longrightarrow> h = height t \<Longrightarrow> size t \<ge> 2^((h+1) div 2) + 2^(h div 2) - 2"
using bound unfolding rbt_def by blast

end
