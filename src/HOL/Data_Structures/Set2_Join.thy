(* Author: Tobias Nipkow *)

section "Join-Based Implementation of Sets"

theory Set2_Join
imports
  Isin2
begin

text \<open>This theory implements the set operations \<open>insert\<close>, \<open>delete\<close>,
\<open>union\<close>, \<open>inter\<close>section and \<open>diff\<close>erence. The implementation is based on binary search trees.
All operations are reduced to a single operation \<open>join l x r\<close> that joins two BSTs \<open>l\<close> and \<open>r\<close>
and an element \<open>x\<close> such that \<open>l < x < r\<close>.

The theory is based on theory \<^theory>\<open>HOL-Data_Structures.Tree2\<close> where nodes have an additional field.
This field is ignored here but it means that this theory can be instantiated
with red-black trees (see theory \<^file>\<open>Set2_Join_RBT.thy\<close>) and other balanced trees.
This approach is very concrete and fixes the type of trees.
Alternatively, one could assume some abstract type \<^typ>\<open>'t\<close> of trees with suitable decomposition
and recursion operators on it.\<close>

locale Set2_Join =
fixes join :: "('a::linorder*'b) tree \<Rightarrow> 'a \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree"
fixes inv :: "('a*'b) tree \<Rightarrow> bool"
assumes set_join: "set_tree (join l a r) = set_tree l \<union> {a} \<union> set_tree r"
assumes bst_join: "bst (Node l (a, b) r) \<Longrightarrow> bst (join l a r)"
assumes inv_Leaf: "inv \<langle>\<rangle>"
assumes inv_join: "\<lbrakk> inv l; inv r \<rbrakk> \<Longrightarrow> inv (join l a r)"
assumes inv_Node: "\<lbrakk> inv (Node l (a,b) r) \<rbrakk> \<Longrightarrow> inv l \<and> inv r"
begin

declare set_join [simp] Let_def[simp]

subsection "\<open>split_min\<close>"

fun split_min :: "('a*'b) tree \<Rightarrow> 'a \<times> ('a*'b) tree" where
"split_min (Node l (a, _) r) =
  (if l = Leaf then (a,r) else let (m,l') = split_min l in (m, join l' a r))"

lemma split_min_set:
  "\<lbrakk> split_min t = (m,t');  t \<noteq> Leaf \<rbrakk> \<Longrightarrow> m \<in> set_tree t \<and> set_tree t = {m} \<union> set_tree t'"
proof(induction t arbitrary: t' rule: tree2_induct)
  case Node thus ?case by(auto split: prod.splits if_splits dest: inv_Node)
next
  case Leaf thus ?case by simp
qed

lemma split_min_bst:
  "\<lbrakk> split_min t = (m,t');  bst t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow>  bst t' \<and> (\<forall>x \<in> set_tree t'. m < x)"
proof(induction t arbitrary: t' rule: tree2_induct)
  case Node thus ?case by(fastforce simp: split_min_set bst_join split: prod.splits if_splits)
next
  case Leaf thus ?case by simp
qed

lemma split_min_inv:
  "\<lbrakk> split_min t = (m,t');  inv t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow>  inv t'"
proof(induction t arbitrary: t' rule: tree2_induct)
  case Node thus ?case by(auto simp: inv_join split: prod.splits if_splits dest: inv_Node)
next
  case Leaf thus ?case by simp
qed


subsection "\<open>join2\<close>"

definition join2 :: "('a*'b) tree \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"join2 l r = (if r = Leaf then l else let (m,r') = split_min r in join l m r')"

lemma set_join2[simp]: "set_tree (join2 l r) = set_tree l \<union> set_tree r"
by(simp add: join2_def split_min_set split: prod.split)

lemma bst_join2: "\<lbrakk> bst l; bst r; \<forall>x \<in> set_tree l. \<forall>y \<in> set_tree r. x < y \<rbrakk>
  \<Longrightarrow> bst (join2 l r)"
by(simp add: join2_def bst_join split_min_set split_min_bst split: prod.split)

lemma inv_join2: "\<lbrakk> inv l; inv r \<rbrakk> \<Longrightarrow> inv (join2 l r)"
by(simp add: join2_def inv_join split_min_set split_min_inv split: prod.split)


subsection "\<open>split\<close>"

fun split :: "('a*'b)tree \<Rightarrow> 'a \<Rightarrow> ('a*'b)tree \<times> bool \<times> ('a*'b)tree" where
"split Leaf k = (Leaf, False, Leaf)" |
"split (Node l (a, _) r) x =
  (case cmp x a of
     LT \<Rightarrow> let (l1,b,l2) = split l x in (l1, b, join l2 a r) |
     GT \<Rightarrow> let (r1,b,r2) = split r x in (join l a r1, b, r2) |
     EQ \<Rightarrow> (l, True, r))"

lemma split: "split t x = (l,b,r) \<Longrightarrow> bst t \<Longrightarrow>
  set_tree l = {a \<in> set_tree t. a < x} \<and> set_tree r = {a \<in> set_tree t. x < a}
  \<and> (b = (x \<in> set_tree t)) \<and> bst l \<and> bst r"
proof(induction t arbitrary: l b r rule: tree2_induct)
  case Leaf thus ?case by simp
next
  case (Node y a b z l c r)
  consider (LT) l1 xin l2 where "(l1,xin,l2) = split y x" 
    and "split \<langle>y, (a, b), z\<rangle> x = (l1, xin, join l2 a z)" and "cmp x a = LT"
  | (GT) r1 xin r2 where "(r1,xin,r2) = split z x" 
    and "split \<langle>y, (a, b), z\<rangle> x = (join y a r1, xin, r2)" and "cmp x a = GT"
  | (EQ) "split \<langle>y, (a, b), z\<rangle> x = (y, True, z)" and "cmp x a = EQ"
    by (force split: cmp_val.splits prod.splits if_splits)

  thus ?case 
  proof cases
    case (LT l1 xin l2)
    with Node.IH(1)[OF \<open>(l1,xin,l2) = split y x\<close>[symmetric]] Node.prems
    show ?thesis by (force intro!: bst_join)
  next
    case (GT r1 xin r2)
    with Node.IH(2)[OF \<open>(r1,xin,r2) = split z x\<close>[symmetric]] Node.prems
    show ?thesis by (force intro!: bst_join)
  next
    case EQ
    with Node.prems show ?thesis by auto
  qed
qed

lemma split_inv: "split t x = (l,b,r) \<Longrightarrow> inv t \<Longrightarrow> inv l \<and> inv r"
proof(induction t arbitrary: l b r rule: tree2_induct)
  case Leaf thus ?case by simp
next
  case Node
  thus ?case by(force simp: inv_join split!: prod.splits if_splits dest!: inv_Node)
qed

declare split.simps[simp del]


subsection "\<open>insert\<close>"

definition insert :: "'a \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"insert x t = (let (l,_,r) = split t x in join l x r)"

lemma set_tree_insert: "bst t \<Longrightarrow> set_tree (insert x t) = {x} \<union> set_tree t"
by(auto simp add: insert_def split split: prod.split)

lemma bst_insert: "bst t \<Longrightarrow> bst (insert x t)"
by(auto simp add: insert_def bst_join dest: split split: prod.split)

lemma inv_insert: "inv t \<Longrightarrow> inv (insert x t)"
by(force simp: insert_def inv_join dest: split_inv split: prod.split)


subsection "\<open>delete\<close>"

definition delete :: "'a \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree" where
"delete x t = (let (l,_,r) = split t x in join2 l r)"

lemma set_tree_delete: "bst t \<Longrightarrow> set_tree (delete x t) = set_tree t - {x}"
by(auto simp: delete_def split split: prod.split)

lemma bst_delete: "bst t \<Longrightarrow> bst (delete x t)"
by(force simp add: delete_def intro: bst_join2 dest: split split: prod.split)

lemma inv_delete: "inv t \<Longrightarrow> inv (delete x t)"
by(force simp: delete_def inv_join2 dest: split_inv split: prod.split)


subsection "\<open>union\<close>"

fun union :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> ('a*'b)tree" where
"union t1 t2 =
  (if t1 = Leaf then t2 else
   if t2 = Leaf then t1 else
   case t1 of Node l1 (a, _) r1 \<Rightarrow>
   let (l2,_ ,r2) = split t2 a;
       l' = union l1 l2; r' = union r1 r2
   in join l' a r')"

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

fun inter :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> ('a*'b)tree" where
"inter t1 t2 =
  (if t1 = Leaf then Leaf else
   if t2 = Leaf then Leaf else
   case t1 of Node l1 (a, _) r1 \<Rightarrow>
   let (l2,b,r2) = split t2 a;
       l' = inter l1 l2; r' = inter r1 r2
   in if b then join l' a r' else join2 l' r')"

declare inter.simps [simp del]

lemma set_tree_inter:
  "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> set_tree (inter t1 t2) = set_tree t1 \<inter> set_tree t2"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  show ?case
  proof (cases t1 rule: tree2_cases)
    case Leaf thus ?thesis by (simp add: inter.simps)
  next
    case [simp]: (Node l1 a _ r1)
    show ?thesis
    proof (cases "t2 = Leaf")
      case True thus ?thesis by (simp add: inter.simps)
    next
      case False
      let ?L1 = "set_tree l1" let ?R1 = "set_tree r1"
      have *: "a \<notin> ?L1 \<union> ?R1" using \<open>bst t1\<close> by (fastforce)
      obtain l2 b r2 where sp: "split t2 a = (l2,b,r2)" using prod_cases3 by blast
      let ?L2 = "set_tree l2" let ?R2 = "set_tree r2" let ?A = "if b then {a} else {}"
      have t2: "set_tree t2 = ?L2 \<union> ?R2 \<union> ?A" and
           **: "?L2 \<inter> ?R2 = {}" "a \<notin> ?L2 \<union> ?R2" "?L1 \<inter> ?R2 = {}" "?L2 \<inter> ?R1 = {}"
        using split[OF sp] \<open>bst t1\<close> \<open>bst t2\<close> by (force, force, force, force, force)
      have IHl: "set_tree (inter l1 l2) = set_tree l1 \<inter> set_tree l2"
        using "1.IH"(1)[OF _ False _ _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have IHr: "set_tree (inter r1 r2) = set_tree r1 \<inter> set_tree r2"
        using "1.IH"(2)[OF _ False _ _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have "set_tree t1 \<inter> set_tree t2 = (?L1 \<union> ?R1 \<union> {a}) \<inter> (?L2 \<union> ?R2 \<union> ?A)"
        by(simp add: t2)
      also have "\<dots> = (?L1 \<inter> ?L2) \<union> (?R1 \<inter> ?R2) \<union> ?A"
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
    by(fastforce simp: inter.simps[of t1 t2] set_tree_inter split
        intro!: bst_join bst_join2 split: tree.split prod.split)
qed

lemma inv_inter: "\<lbrakk> inv t1; inv t2 \<rbrakk> \<Longrightarrow> inv (inter t1 t2)"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  thus ?case
    by(auto simp: inter.simps[of t1 t2] inv_join inv_join2 split_inv
        split!: tree.split prod.split dest: inv_Node)
qed

subsection "\<open>diff\<close>"

fun diff :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> ('a*'b)tree" where
"diff t1 t2 =
  (if t1 = Leaf then Leaf else
   if t2 = Leaf then t1 else
   case t2 of Node l2 (a, _) r2 \<Rightarrow>
   let (l1,_,r1) = split t1 a;
       l' = diff l1 l2; r' = diff r1 r2
   in join2 l' r')"

declare diff.simps [simp del]

lemma set_tree_diff:
  "\<lbrakk> bst t1; bst t2 \<rbrakk> \<Longrightarrow> set_tree (diff t1 t2) = set_tree t1 - set_tree t2"
proof(induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  show ?case
  proof (cases t2 rule: tree2_cases)
    case Leaf thus ?thesis by (simp add: diff.simps)
  next
    case [simp]: (Node l2 a _ r2)
    show ?thesis
    proof (cases "t1 = Leaf")
      case True thus ?thesis by (simp add: diff.simps)
    next
      case False
      let ?L2 = "set_tree l2" let ?R2 = "set_tree r2"
      obtain l1 b r1 where sp: "split t1 a = (l1,b,r1)" using prod_cases3 by blast
      let ?L1 = "set_tree l1" let ?R1 = "set_tree r1" let ?A = "if b then {a} else {}"
      have t1: "set_tree t1 = ?L1 \<union> ?R1 \<union> ?A" and
           **: "a \<notin> ?L1 \<union> ?R1" "?L1 \<inter> ?R2 = {}" "?L2 \<inter> ?R1 = {}"
        using split[OF sp] \<open>bst t1\<close> \<open>bst t2\<close> by (force, force, force, force)
      have IHl: "set_tree (diff l1 l2) = set_tree l1 - set_tree l2"
        using "1.IH"(1)[OF False _ _ _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have IHr: "set_tree (diff r1 r2) = set_tree r1 - set_tree r2"
        using "1.IH"(2)[OF False _ _ _ sp[symmetric]] "1.prems"(1,2) split[OF sp] by simp
      have "set_tree t1 - set_tree t2 = (?L1 \<union> ?R1) - (?L2 \<union> ?R2  \<union> {a})"
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
    by(fastforce simp: diff.simps[of t1 t2] set_tree_diff split
        intro!: bst_join bst_join2 split: tree.split prod.split)
qed

lemma inv_diff: "\<lbrakk> inv t1; inv t2 \<rbrakk> \<Longrightarrow> inv (diff t1 t2)"
proof(induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  thus ?case
    by(auto simp: diff.simps[of t1 t2] inv_join inv_join2 split_inv
        split!: tree.split prod.split dest: inv_Node)
qed

text \<open>Locale \<^locale>\<open>Set2_Join\<close> implements locale \<^locale>\<open>Set2\<close>:\<close>

sublocale Set2
where empty = Leaf and insert = insert and delete = delete and isin = isin
and union = union and inter = inter and diff = diff
and set = set_tree and invar = "\<lambda>t. inv t \<and> bst t"
proof (standard, goal_cases)
  case 1 show ?case by (simp)
next
  case 2 thus ?case by(simp add: isin_set_tree)
next
  case 3 thus ?case by (simp add: set_tree_insert)
next
  case 4 thus ?case by (simp add: set_tree_delete)
next
  case 5 thus ?case by (simp add: inv_Leaf)
next
  case 6 thus ?case by (simp add: bst_insert inv_insert)
next
  case 7 thus ?case by (simp add: bst_delete inv_delete)
next
  case 8 thus ?case by(simp add: set_tree_union)
next
  case 9 thus ?case by(simp add: set_tree_inter)
next
  case 10 thus ?case by(simp add: set_tree_diff)
next
  case 11 thus ?case by (simp add: bst_union inv_union)
next
  case 12 thus ?case by (simp add: bst_inter inv_inter)
next
  case 13 thus ?case by (simp add: bst_diff inv_diff)
qed

end

interpretation unbal: Set2_Join
where join = "\<lambda>l x r. Node l (x, ()) r" and inv = "\<lambda>t. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by simp
next
  case 3 thus ?case by simp
next
  case 4 thus ?case by simp
next
  case 5 thus ?case by simp
qed

end