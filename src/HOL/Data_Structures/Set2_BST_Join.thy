(* Author: Tobias Nipkow *)

section "Join-Based BST Implementation of Sets"

theory Set2_BST_Join
imports
  "HOL-Library.Tree"
  Cmp
  Set_Specs
begin

text \<open>This theory implements the set operations \<open>insert\<close>, \<open>delete\<close>,
\<open>union\<close>, \<open>inter\<close>section and \<open>diff\<close>erence. The implementation is based on binary search trees.
All operations are reduced to a single operation \<open>join l x r\<close> that joins two BSTs \<open>l\<close> and \<open>r\<close>
and an element \<open>x\<close> such that \<open>l < x < r\<close>.

This theory illustrates the idea but is not suitable for an efficient implementation where
\<open>join\<close> balances the tree in some manner because type @{typ "'a tree"} in theory @{theory Tree}
has no additional fields for recording balance information. See theory \<open>Set2_BST2_Join\<close> for that.\<close>

text \<open>Function \<open>isin\<close> can also be expressed via \<open>join\<close> but this is more direct:\<close>

fun isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)"

lemma isin_set: "bst t \<Longrightarrow> isin t x = (x \<in> set_tree t)"
by (induction t) (auto)


locale Set2_BST_Join =
fixes join :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
assumes set_join: "set_tree (join t1 x t2) = Set.insert x (set_tree t1 \<union> set_tree t2)"
assumes bst_join:
  "\<lbrakk> bst l; bst r; \<forall>x \<in> set_tree l. x < k; \<forall>y \<in> set_tree r. k < y \<rbrakk>
  \<Longrightarrow> bst (join l k r)"
fixes inv :: "'a tree \<Rightarrow> bool"
assumes inv_Leaf: "inv \<langle>\<rangle>"
assumes inv_join: "\<lbrakk> inv l; inv r \<rbrakk> \<Longrightarrow> inv (join l k r)"
assumes inv_Node: "\<lbrakk> inv (Node l x r) \<rbrakk> \<Longrightarrow> inv l \<and> inv r"
begin

declare set_join [simp]

subsection "\<open>split_min\<close>"

fun split_min :: "'a tree \<Rightarrow> 'a \<times> 'a tree" where
"split_min (Node l x r) =
  (if l = Leaf then (x,r) else let (m,l') = split_min l in (m, join l' x r))"

lemma split_min_set:
  "\<lbrakk> split_min t = (x,t');  t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   x \<in> set_tree t \<and> set_tree t = Set.insert x (set_tree t')"
proof(induction t arbitrary: t')
  case Node thus ?case by(auto split: prod.splits if_splits)
next
  case Leaf thus ?case by simp
qed

lemma split_min_bst:
  "\<lbrakk> split_min t = (x,t');  bst t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow>  bst t' \<and> (\<forall>x' \<in> set_tree t'. x < x')"
proof(induction t arbitrary: t')
  case Node thus ?case by(fastforce simp: split_min_set bst_join split: prod.splits if_splits)
next
  case Leaf thus ?case by simp
qed

lemma split_min_inv:
  "\<lbrakk> split_min t = (x,t');  inv t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow>  inv t'"
proof(induction t arbitrary: t')
  case Node thus ?case by(auto simp: inv_join split: prod.splits if_splits dest: inv_Node)
next
  case Leaf thus ?case by simp
qed


subsection "\<open>join2\<close>"

definition join2 :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"join2 l r = (if r = Leaf then l else let (x,r') = split_min r in join l x r')"

lemma set_join2[simp]: "set_tree (join2 l r) = set_tree l \<union> set_tree r"
by(simp add: join2_def split_min_set split: prod.split)

lemma bst_join2: "\<lbrakk> bst l; bst r; \<forall>x \<in> set_tree l. \<forall>y \<in> set_tree r. x < y \<rbrakk>
  \<Longrightarrow> bst (join2 l r)"
by(simp add: join2_def bst_join split_min_set split_min_bst split: prod.split)

lemma inv_join2: "\<lbrakk> inv l; inv r \<rbrakk> \<Longrightarrow> inv (join2 l r)"
by(simp add: join2_def inv_join split_min_set split_min_inv split: prod.split)


subsection "\<open>split\<close>"

fun split :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<times> bool \<times> 'a tree" where
"split Leaf k = (Leaf, False, Leaf)" |
"split (Node l a r) k =
  (case cmp k a of
    LT \<Rightarrow> let (l1,b,l2) = split l k in (l1, b, join l2 a r) |
    GT \<Rightarrow> let (r1,b,r2) = split r k in (join l a r1, b, r2) |
    EQ \<Rightarrow> (l, True, r))"

lemma split: "split t k = (l,kin,r) \<Longrightarrow> bst t \<Longrightarrow>
  set_tree l = {x \<in> set_tree t. x < k} \<and> set_tree r = {x \<in> set_tree t. k < x}
  \<and> (kin = (k \<in> set_tree t)) \<and> bst l \<and> bst r"
proof(induction t arbitrary: l kin r)
  case Leaf thus ?case by simp
next
  case Node thus ?case by(force split!: prod.splits if_splits intro!: bst_join)
qed

lemma split_inv: "split t k = (l,kin,r) \<Longrightarrow> inv t \<Longrightarrow> inv l \<and> inv r"
proof(induction t arbitrary: l kin r)
  case Leaf thus ?case by simp
next
  case Node
  thus ?case by(force simp: inv_join split!: prod.splits if_splits dest!: inv_Node)
qed

declare split.simps[simp del]


subsection "\<open>insert\<close>"

definition insert :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert k t = (let (l,_,r) = split t k in join l k r)"

lemma set_tree_insert: "bst t \<Longrightarrow> set_tree (insert x t) = Set.insert x (set_tree t)"
by(auto simp add: insert_def split split: prod.split)

lemma bst_insert: "bst t \<Longrightarrow> bst (insert x t)"
by(auto simp add: insert_def bst_join dest: split split: prod.split)

lemma inv_insert: "inv t \<Longrightarrow> inv (insert x t)"
by(force simp: insert_def inv_join dest: split_inv split: prod.split)


subsection "\<open>delete\<close>"

definition delete :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete k t = (let (l,_,r) = split t k in join2 l r)"

lemma set_tree_delete: "bst t \<Longrightarrow> set_tree (delete k t) = set_tree t - {k}"
by(auto simp: delete_def split split: prod.split)

lemma bst_delete: "bst t \<Longrightarrow> bst (delete x t)"
by(force simp add: delete_def intro: bst_join2 dest: split split: prod.split)

lemma inv_delete: "inv t \<Longrightarrow> inv (delete x t)"
by(force simp: delete_def inv_join2 dest: split_inv split: prod.split)


subsection "\<open>union\<close>"

fun union :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"union t1 t2 =
  (if t1 = Leaf then t2 else
   if t2 = Leaf then t1 else
   case t1 of Node l1 k r1 \<Rightarrow>
   let (l2,_ ,r2) = split t2 k;
       l' = union l1 l2; r' = union r1 r2
   in join l' k r')"

declare union.simps [simp del]

lemma set_tree_union: "bst t2 \<Longrightarrow> set_tree (union t1 t2) = set_tree t1 \<union> set_tree t2"
proof(induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  then show ?case
    by (auto simp: union.simps[of t1 t2] split split: tree.split prod.split)
qed

lemma bst_union: "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> bst (union t1 t2)"
proof(induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  thus ?case
    by(fastforce simp: union.simps[of t1 t2] set_tree_union split intro!: bst_join 
        split: tree.split prod.split)
qed

lemma inv_union: "\<lbrakk> inv t1; inv t2 \<rbrakk> \<Longrightarrow> inv (union t1 t2)"
proof(induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  thus ?case
    by(auto simp:union.simps[of t1 t2] inv_join split_inv
        split!: tree.split prod.split dest: inv_Node)
qed

subsection "\<open>inter\<close>"

fun inter :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"inter t1 t2 =
  (if t1 = Leaf then Leaf else
   if t2 = Leaf then Leaf else
   case t1 of Node l1 k r1 \<Rightarrow>
   let (l2,kin,r2) = split t2 k;
       l' = inter l1 l2; r' = inter r1 r2
   in if kin then join l' k r' else join2 l' r')"

declare inter.simps [simp del]

lemma set_tree_inter:
  "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> set_tree (inter t1 t2) = set_tree t1 \<inter> set_tree t2"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  show ?case
  proof (cases t1)
    case Leaf thus ?thesis by (simp add: inter.simps)
  next
    case [simp]: (Node l1 k r1)
    show ?thesis
    proof (cases "t2 = Leaf")
      case True thus ?thesis by (simp add: inter.simps)
    next
      case False
      let ?L1 = "set_tree l1" let ?R1 = "set_tree r1"
      have *: "k \<notin> ?L1 \<union> ?R1" using \<open>bst t1\<close> by (fastforce)
      obtain l2 kin r2 where sp: "split t2 k = (l2,kin,r2)" using prod_cases3 by blast
      let ?L2 = "set_tree l2" let ?R2 = "set_tree r2" let ?K = "if kin then {k} else {}"
      have t2: "set_tree t2 = ?L2 \<union> ?R2 \<union> ?K" and
           **: "?L2 \<inter> ?R2 = {}" "k \<notin> ?L2 \<union> ?R2" "?L1 \<inter> ?R2 = {}" "?L2 \<inter> ?R1 = {}"
        using split[OF sp] \<open>bst t1\<close> \<open>bst t2\<close> by (force, force, force, force, force)
      have IHl: "set_tree (inter l1 l2) = set_tree l1 \<inter> set_tree l2"
        using "1.IH"(1)[OF _ False _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have IHr: "set_tree (inter r1 r2) = set_tree r1 \<inter> set_tree r2"
        using "1.IH"(2)[OF _ False _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have "set_tree t1 \<inter> set_tree t2 = (?L1 \<union> ?R1 \<union> {k}) \<inter> (?L2 \<union> ?R2 \<union> ?K)"
        by(simp add: t2)
      also have "\<dots> = (?L1 \<inter> ?L2) \<union> (?R1 \<inter> ?R2) \<union> ?K"
        using * ** by auto
      also have "\<dots> = set_tree (inter t1 t2)"
      using IHl IHr sp inter.simps[of t1 t2] False by(simp)
      finally show ?thesis by simp
    qed
  qed
qed

lemma bst_inter: "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> bst (inter t1 t2)"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  thus ?case
    by(fastforce simp: inter.simps[of t1 t2] set_tree_inter split Let_def
        intro!: bst_join bst_join2 split: tree.split prod.split)
qed

lemma inv_inter: "\<lbrakk> inv t1; inv t2 \<rbrakk> \<Longrightarrow> inv (inter t1 t2)"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  thus ?case
    by(auto simp: inter.simps[of t1 t2] inv_join inv_join2 split_inv Let_def
        split!: tree.split prod.split dest: inv_Node)
qed

subsection "\<open>diff\<close>"

fun diff :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"diff t1 t2 =
  (if t1 = Leaf then Leaf else
   if t2 = Leaf then t1 else
   case t2 of Node l2 k r2 \<Rightarrow>
   let (l1,_,r1) = split t1 k;
       l' = diff l1 l2; r' = diff r1 r2
   in join2 l' r')"

declare diff.simps [simp del]

lemma set_tree_diff:
  "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> set_tree (diff t1 t2) = set_tree t1 - set_tree t2"
proof(induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  show ?case
  proof (cases t2)
    case Leaf thus ?thesis by (simp add: diff.simps)
  next
    case [simp]: (Node l2 k r2)
    show ?thesis
    proof (cases "t1 = Leaf")
      case True thus ?thesis by (simp add: diff.simps)
    next
      case False
      let ?L2 = "set_tree l2" let ?R2 = "set_tree r2"
      obtain l1 kin r1 where sp: "split t1 k = (l1,kin,r1)" using prod_cases3 by blast
      let ?L1 = "set_tree l1" let ?R1 = "set_tree r1" let ?K = "if kin then {k} else {}"
      have t1: "set_tree t1 = ?L1 \<union> ?R1 \<union> ?K" and
           **: "k \<notin> ?L1 \<union> ?R1" "?L1 \<inter> ?R2 = {}" "?L2 \<inter> ?R1 = {}"
        using split[OF sp] \<open>bst t1\<close> \<open>bst t2\<close> by (force, force, force, force)
      have IHl: "set_tree (diff l1 l2) = set_tree l1 - set_tree l2"
        using "1.IH"(1)[OF False _ _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have IHr: "set_tree (diff r1 r2) = set_tree r1 - set_tree r2"
        using "1.IH"(2)[OF False _ _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have "set_tree t1 - set_tree t2 = (?L1 \<union> ?R1) - (?L2 \<union> ?R2  \<union> {k})"
        by(simp add: t1)
      also have "\<dots> = (?L1 - ?L2) \<union> (?R1 - ?R2)"
        using ** by auto
      also have "\<dots> = set_tree (diff t1 t2)"
      using IHl IHr sp diff.simps[of t1 t2] False by(simp)
      finally show ?thesis by simp
    qed
  qed
qed

lemma bst_diff: "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> bst (diff t1 t2)"
proof(induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  thus ?case
    by(fastforce simp: diff.simps[of t1 t2] set_tree_diff split Let_def
        intro!: bst_join bst_join2 split: tree.split prod.split)
qed

lemma inv_diff: "\<lbrakk> inv t1; inv t2 \<rbrakk> \<Longrightarrow> inv (diff t1 t2)"
proof(induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  thus ?case
    by(auto simp: diff.simps[of t1 t2] inv_join inv_join2 split_inv Let_def
        split!: tree.split prod.split dest: inv_Node)
qed

text \<open>Locale @{locale Set2_BST_Join} implements locale @{locale Set2}:\<close>

sublocale Set2
where empty = Leaf and isin = isin and insert = insert and delete = delete
and  union = union and inter = inter and diff = diff
and set = set_tree and invar = "\<lambda>t. bst t \<and> inv t"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by (simp add: isin_set)
next
  case 3 thus ?case by (simp add: set_tree_insert)
next
  case 4 thus ?case by (simp add: set_tree_delete)
next
  case 5 thus ?case by (simp add: inv_Leaf)
next
  case 6 thus ?case by (simp add: inv_insert bst_insert)
next
  case 7 thus ?case by (simp add: inv_delete bst_delete)
next
  case 8 thus ?case by (simp add: set_tree_union)
next
  case 9 thus ?case by (simp add: set_tree_inter)
next
  case 10 thus ?case by (simp add: set_tree_diff)
next
  case 11 thus ?case by (simp add: bst_union inv_union)
next
  case 12 thus ?case by (simp add: bst_inter inv_inter)
next
  case 13 thus ?case by (simp add: bst_diff inv_diff)
qed

end (* Set2_BST_Join *)

text \<open>Interpretation of @{locale Set2_BST_Join} with unbalanced binary trees:\<close>

interpretation Set2_BST_Join where join = Node and inv = "\<lambda>t. True"
proof (standard, goal_cases)
qed auto

end