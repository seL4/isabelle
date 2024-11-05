(* Author: Tobias Nipkow *)

section "Join-Based Implementation of Sets via RBTs"

theory Set2_Join_RBT
imports
  Set2_Join
  RBT_Set
begin

subsection "Code"

text \<open>
Function \<open>joinL\<close> joins two trees (and an element).
Precondition: \<^prop>\<open>bheight l \<le> bheight r\<close>.
Method:
Descend along the left spine of \<open>r\<close>
until you find a subtree with the same \<open>bheight\<close> as \<open>l\<close>,
then combine them into a new red node.
\<close>
fun joinL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"joinL l x r =
  (if bheight l \<ge> bheight r then R l x r
   else case r of
     B l' x' r' \<Rightarrow> baliL (joinL l x l') x' r' |
     R l' x' r' \<Rightarrow> R (joinL l x l') x' r')"

fun joinR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"joinR l x r =
  (if bheight l \<le> bheight r then R l x r
   else case l of
     B l' x' r' \<Rightarrow> baliR l' x' (joinR r' x r) |
     R l' x' r' \<Rightarrow> R l' x' (joinR r' x r))"

definition join :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"join l x r =
  (if bheight l > bheight r
   then paint Black (joinR l x r)
   else if bheight l < bheight r
   then paint Black (joinL l x r)
   else B l x r)"

declare joinL.simps[simp del]
declare joinR.simps[simp del]


subsection "Properties"

subsubsection "Color and height invariants"

lemma invc2_joinL:
 "\<lbrakk> invc l; invc r; bheight l \<le> bheight r \<rbrakk> \<Longrightarrow>
  invc2 (joinL l x r)
  \<and> (bheight l \<noteq> bheight r \<and> color r = Black \<longrightarrow> invc(joinL l x r))"
proof (induct l x r rule: joinL.induct)
  case (1 l x r) thus ?case
    by(auto simp: invc_baliL invc2I joinL.simps[of l x r] split!: tree.splits if_splits)
qed

lemma invc2_joinR:
  "\<lbrakk> invc l; invh l; invc r; invh r; bheight l \<ge> bheight r \<rbrakk> \<Longrightarrow>
  invc2 (joinR l x r)
  \<and> (bheight l \<noteq> bheight r \<and> color l = Black \<longrightarrow> invc(joinR l x r))"
proof (induct l x r rule: joinR.induct)
  case (1 l x r) thus ?case
    by(fastforce simp: invc_baliR invc2I joinR.simps[of l x r] split!: tree.splits if_splits)
qed

lemma bheight_joinL:
  "\<lbrakk> invh l; invh r; bheight l \<le> bheight r \<rbrakk> \<Longrightarrow> bheight (joinL l x r) = bheight r"
proof (induct l x r rule: joinL.induct)
  case (1 l x r) thus ?case
    by(auto simp: bheight_baliL joinL.simps[of l x r] split!: tree.split)
qed

lemma invh_joinL:
  "\<lbrakk> invh l;  invh r;  bheight l \<le> bheight r \<rbrakk> \<Longrightarrow> invh (joinL l x r)"
proof (induct l x r rule: joinL.induct)
  case (1 l x r) thus ?case
    by(auto simp: invh_baliL bheight_joinL joinL.simps[of l x r] split!: tree.split color.split)
qed

lemma bheight_joinR:
  "\<lbrakk> invh l;  invh r;  bheight l \<ge> bheight r \<rbrakk> \<Longrightarrow> bheight (joinR l x r) = bheight l"
proof (induct l x r rule: joinR.induct)
  case (1 l x r) thus ?case
    by(fastforce simp: bheight_baliR joinR.simps[of l x r] split!: tree.split)
qed

lemma invh_joinR:
  "\<lbrakk> invh l; invh r; bheight l \<ge> bheight r \<rbrakk> \<Longrightarrow> invh (joinR l x r)"
proof (induct l x r rule: joinR.induct)
  case (1 l x r) thus ?case
    by(fastforce simp: invh_baliR bheight_joinR joinR.simps[of l x r]
        split!: tree.split color.split)
qed

text \<open>All invariants in one:\<close>

lemma inv_joinL: "\<lbrakk> invc l; invc r; invh l; invh r; bheight l \<le> bheight r \<rbrakk>
 \<Longrightarrow> invc2 (joinL l x r) \<and> (bheight l \<noteq> bheight r \<and> color r = Black \<longrightarrow>  invc (joinL l x r))
     \<and> invh (joinL l x r) \<and> bheight (joinL l x r) = bheight r"
proof (induct l x r rule: joinL.induct)
  case (1 l x r) thus ?case
    by(auto simp: inv_baliL invc2I joinL.simps[of l x r] split!: tree.splits if_splits)
qed

lemma inv_joinR: "\<lbrakk> invc l; invc r; invh l; invh r; bheight l \<ge> bheight r \<rbrakk>
 \<Longrightarrow> invc2 (joinR l x r) \<and> (bheight l \<noteq> bheight r \<and> color l = Black \<longrightarrow>  invc (joinR l x r))
     \<and> invh (joinR l x r) \<and> bheight (joinR l x r) = bheight l"
proof (induct l x r rule: joinR.induct)
  case (1 l x r) thus ?case
    by(auto simp: inv_baliR invc2I joinR.simps[of l x r] split!: tree.splits if_splits)
qed

(* unused *)
lemma rbt_join: "\<lbrakk> invc l; invh l; invc r; invh r \<rbrakk> \<Longrightarrow> rbt(join l x r)"
by(simp add: inv_joinL inv_joinR invh_paint rbt_def color_paint_Black join_def)

text \<open>To make sure the the black height is not increased unnecessarily:\<close>

lemma bheight_paint_Black: "bheight(paint Black t) \<le> bheight t + 1"
by(cases t) auto

lemma "\<lbrakk> rbt l; rbt r \<rbrakk> \<Longrightarrow> bheight(join l x r) \<le> max (bheight l) (bheight r) + 1"
using bheight_paint_Black[of "joinL l x r"] bheight_paint_Black[of "joinR l x r"]
  bheight_joinL[of l r x] bheight_joinR[of l r x]
by(auto simp: max_def rbt_def join_def)


subsubsection "Inorder properties"

text "Currently unused. Instead \<^const>\<open>set_tree\<close> and \<^const>\<open>bst\<close> properties are proved directly."

lemma inorder_joinL: "bheight l \<le> bheight r \<Longrightarrow> inorder(joinL l x r) = inorder l @ x # inorder r"
proof(induction l x r rule: joinL.induct)
  case (1 l x r)
  thus ?case by(auto simp: inorder_baliL joinL.simps[of l x r] split!: tree.splits color.splits)
qed

lemma inorder_joinR:
  "inorder(joinR l x r) = inorder l @ x # inorder r"
proof(induction l x r rule: joinR.induct)
  case (1 l x r)
  thus ?case by (force simp: inorder_baliR joinR.simps[of l x r] split!: tree.splits color.splits)
qed

lemma "inorder(join l x r) = inorder l @ x # inorder r"
by(auto simp: inorder_joinL inorder_joinR inorder_paint join_def
      split!: tree.splits color.splits if_splits
      dest!: arg_cong[where f = inorder])


subsubsection "Set and bst properties"

lemma set_baliL:
  "set_tree(baliL l a r) = set_tree l \<union> {a} \<union> set_tree r"
by(cases "(l,a,r)" rule: baliL.cases) (auto)

lemma set_joinL:
  "bheight l \<le> bheight r \<Longrightarrow> set_tree (joinL l x r) = set_tree l \<union> {x} \<union> set_tree r"
proof(induction l x r rule: joinL.induct)
  case (1 l x r)
  thus ?case by(auto simp: set_baliL joinL.simps[of l x r] split!: tree.splits color.splits)
qed

lemma set_baliR:
  "set_tree(baliR l a r) = set_tree l \<union> {a} \<union> set_tree r"
by(cases "(l,a,r)" rule: baliR.cases) (auto)

lemma set_joinR:
  "set_tree (joinR l x r) = set_tree l \<union> {x} \<union> set_tree r"
proof(induction l x r rule: joinR.induct)
  case (1 l x r)
  thus ?case by(force simp: set_baliR joinR.simps[of l x r] split!: tree.splits color.splits)
qed

lemma set_paint: "set_tree (paint c t) = set_tree t"
by (cases t) auto

lemma set_join: "set_tree (join l x r) = set_tree l \<union> {x} \<union> set_tree r"
by(simp add: set_joinL set_joinR set_paint join_def)

lemma bst_baliL:
  "\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>x\<in>set_tree r. a < x\<rbrakk>
   \<Longrightarrow> bst (baliL l a r)"
by(cases "(l,a,r)" rule: baliL.cases) (auto simp: ball_Un)

lemma bst_baliR:
  "\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>x\<in>set_tree r. a < x\<rbrakk>
   \<Longrightarrow> bst (baliR l a r)"
by(cases "(l,a,r)" rule: baliR.cases) (auto simp: ball_Un)

lemma bst_joinL:
  "\<lbrakk>bst (Node l (a, n) r); bheight l \<le> bheight r\<rbrakk>
  \<Longrightarrow> bst (joinL l a r)"
proof(induction l a r rule: joinL.induct)
  case (1 l a r)
  thus ?case
    by(auto simp: set_baliL joinL.simps[of l a r] set_joinL ball_Un intro!: bst_baliL
        split!: tree.splits color.splits)
qed

lemma bst_joinR:
  "\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y \<rbrakk>
  \<Longrightarrow> bst (joinR l a r)"
proof(induction l a r rule: joinR.induct)
  case (1 l a r)
  thus ?case
    by(auto simp: set_baliR joinR.simps[of l a r] set_joinR ball_Un intro!: bst_baliR
        split!: tree.splits color.splits)
qed

lemma bst_paint: "bst (paint c t) = bst t"
by(cases t) auto

lemma bst_join:
  "bst (Node l (a, n) r) \<Longrightarrow> bst (join l a r)"
by(auto simp: bst_paint bst_joinL bst_joinR join_def)

lemma inv_join: "\<lbrakk> invc l; invh l; invc r; invh r \<rbrakk> \<Longrightarrow> invc(join l x r) \<and> invh(join l x r)"
by (simp add: inv_joinL inv_joinR invh_paint join_def)

subsubsection "Interpretation of \<^locale>\<open>Set2_Join\<close> with Red-Black Tree"

global_interpretation RBT: Set2_Join
where join = join and inv = "\<lambda>t. invc t \<and> invh t"
defines insert_rbt = RBT.insert and delete_rbt = RBT.delete and split_rbt = RBT.split
and join2_rbt = RBT.join2 and split_min_rbt = RBT.split_min
and inter_rbt = RBT.inter and union_rbt = RBT.union and diff_rbt = RBT.diff 
proof (standard, goal_cases)
  case 1 show ?case by (rule set_join)
next
  case 2 thus ?case by (simp add: bst_join)
next
  case 3 show ?case by simp
next
  case 4 thus ?case by (simp add: inv_join)
next
  case 5 thus ?case by simp
qed

text \<open>The invariant does not guarantee that the root node is black. This is not required
to guarantee that the height is logarithmic in the size --- Exercise.\<close>

end