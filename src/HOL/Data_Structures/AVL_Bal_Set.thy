(* Tobias Nipkow *)

section "AVL Tree with Balance Tags (Set Implementation)"

theory AVL_Bal_Set
imports
  Cmp
  Isin2
begin

datatype bal = Lh | Bal | Rh
(* Exercise: use 3 Node constructors instead *)

type_synonym 'a tree_bal = "('a * bal) tree"

text \<open>Invariant:\<close>

fun avl :: "'a tree_bal \<Rightarrow> bool" where
"avl Leaf = True" |
"avl (Node l (a,b) r) =
  ((case b of
    Bal \<Rightarrow> height r = height l |
    Lh \<Rightarrow> height l = height r + 1 |
    Rh \<Rightarrow> height r = height l + 1)
  \<and> avl l \<and> avl r)"


subsection \<open>Code\<close>

datatype 'a change = Same 'a | Diff 'a

fun tree :: "'a change \<Rightarrow> 'a" where
"tree(Same t) = t" |
"tree(Diff t) = t"

fun rot21 :: "bal \<Rightarrow> bal" where
"rot21 b = (if b=Rh then Lh else Bal)"

fun rot22 :: "bal \<Rightarrow> bal" where
"rot22 b = (if b=Lh then Rh else Bal)"

fun balL :: "'a tree_bal change \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal change" where
"balL AB' c bc C = (case AB' of
   Same AB \<Rightarrow> Same (Node AB (c,bc) C) |
   Diff AB \<Rightarrow> (case bc of
     Bal \<Rightarrow> Diff (Node AB (c,Lh) C) |
     Rh \<Rightarrow> Same (Node AB (c,Bal) C) |
     Lh \<Rightarrow> Same(case AB of
       Node A (a,Lh) B \<Rightarrow> Node A (a,Bal) (Node B (c,Bal) C) |
       Node A (a,Rh) B \<Rightarrow> (case B of
         Node B\<^sub>1 (b, bb) B\<^sub>2 \<Rightarrow>
           Node (Node A (a,rot21 bb) B\<^sub>1) (b,Bal) (Node B\<^sub>2 (c,rot22 bb) C)))))"

fun balR :: "'a tree_bal \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal change \<Rightarrow> 'a tree_bal change" where
"balR A a ba BC' = (case BC' of
   Same BC \<Rightarrow> Same (Node A (a,ba) BC) |
   Diff BC \<Rightarrow> (case ba of
     Bal \<Rightarrow> Diff (Node A (a,Rh) BC) |
     Lh \<Rightarrow> Same (Node A (a,Bal) BC) |
     Rh \<Rightarrow> Same(case BC of
       Node B (c,Rh) C \<Rightarrow> Node (Node A (a,Bal) B) (c,Bal) C |
       Node B (c,Lh) C \<Rightarrow> (case B of
         Node B\<^sub>1 (b, bb) B\<^sub>2 \<Rightarrow>
           Node (Node A (a,rot21 bb) B\<^sub>1) (b,Bal) (Node B\<^sub>2 (c,rot22 bb) C)))))"

fun insert :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal change" where
"insert x Leaf = Diff(Node Leaf (x, Bal) Leaf)" |
"insert x (Node l (a, b) r) = (case cmp x a of
   EQ \<Rightarrow> Same(Node l (a, b) r) |
   LT \<Rightarrow> balL (insert x l) a b r |
   GT \<Rightarrow> balR l a b (insert x r))"

fun baldR :: "'a tree_bal \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal change \<Rightarrow> 'a tree_bal change" where
"baldR AB c bc C' = (case C' of
   Same C \<Rightarrow> Same (Node AB (c,bc) C) |
   Diff C \<Rightarrow> (case bc of
     Bal \<Rightarrow> Same (Node AB (c,Lh) C) |
     Rh \<Rightarrow> Diff (Node AB (c,Bal) C) |
     Lh \<Rightarrow> (case AB of
       Node A (a,Lh) B \<Rightarrow> Diff(Node A (a,Bal) (Node B (c,Bal) C)) |
       Node A (a,Bal) B \<Rightarrow> Same(Node A (a,Rh) (Node B (c,Lh) C)) |
       Node A (a,Rh) B \<Rightarrow> (case B of
         Node B\<^sub>1 (b, bb) B\<^sub>2 \<Rightarrow>
           Diff(Node (Node A (a,rot21 bb) B\<^sub>1) (b,Bal) (Node B\<^sub>2 (c,rot22 bb) C))))))"

fun baldL :: "'a tree_bal change \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal change" where
"baldL A' a ba BC = (case A' of
   Same A \<Rightarrow> Same (Node A (a,ba) BC) |
   Diff A \<Rightarrow> (case ba of
     Bal \<Rightarrow> Same (Node A (a,Rh) BC) |
     Lh \<Rightarrow> Diff (Node A (a,Bal) BC) |
     Rh \<Rightarrow> (case BC of
       Node B (c,Rh) C \<Rightarrow> Diff(Node (Node A (a,Bal) B) (c,Bal) C) |
       Node B (c,Bal) C \<Rightarrow> Same(Node (Node A (a,Rh) B) (c,Lh) C) |
       Node B (c,Lh) C \<Rightarrow> (case B of
         Node B\<^sub>1 (b, bb) B\<^sub>2 \<Rightarrow>
           Diff(Node (Node A (a,rot21 bb) B\<^sub>1) (b,Bal) (Node B\<^sub>2 (c,rot22 bb) C))))))"

fun split_max :: "'a tree_bal \<Rightarrow> 'a tree_bal change * 'a" where
"split_max (Node l (a, ba) r) =
  (if r = Leaf then (Diff l,a) else let (r',a') = split_max r in (baldR l a ba r', a'))"

fun delete :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal change" where
"delete _ Leaf = Same Leaf" |
"delete x (Node l (a, ba) r) =
  (case cmp x a of
     EQ \<Rightarrow> if l = Leaf then Diff r
           else let (l', a') = split_max l in baldL l' a' ba r |
     LT \<Rightarrow> baldL (delete x l) a ba r |
     GT \<Rightarrow> baldR l a ba (delete x r))"

lemmas split_max_induct = split_max.induct[case_names Node Leaf]

lemmas splits =  if_splits tree.splits tree.splits change.splits bal.splits

subsection \<open>Proofs\<close>

lemma insert_Diff1[simp]: "insert x t \<noteq> Diff Leaf"
by (cases t)(auto split!: splits)

lemma insert_Diff2[simp]: "insert x t = Diff (Node l (a,Bal) r) \<longleftrightarrow> t = Leaf \<and> a = x \<and> l=Leaf \<and> r=Leaf"
by (cases t)(auto split!: splits)

lemma insert_Diff3[simp]: "insert x t \<noteq> Diff (Node l (a,Rh) Leaf)"
by (cases t)(auto split!: splits)

lemma insert_Diff4[simp]: "insert x t \<noteq> Diff (Node Leaf (a,Lh) r)"
by (cases t)(auto split!: splits)


subsubsection "Proofs for insert"

theorem inorder_insert:
  "\<lbrakk> avl t;  sorted(inorder t) \<rbrakk> \<Longrightarrow> inorder(tree(insert x t)) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps split!: splits)

lemma avl_insert_case: "avl t \<Longrightarrow> case insert x t of
   Same t' \<Rightarrow> avl t' \<and> height t' = height t |
   Diff t' \<Rightarrow> avl t' \<and> height t' = height t + 1"
apply(induction x t rule: insert.induct)
apply(auto simp: max_absorb1 split!: splits)
done

corollary avl_insert: "avl t \<Longrightarrow> avl(tree(insert x t))"
using avl_insert_case[of t x] by (simp split: splits)


subsubsection "Proofs for delete"

lemma inorder_baldL:
  "\<lbrakk> ba = Rh \<longrightarrow> r \<noteq> Leaf; avl r \<rbrakk>
  \<Longrightarrow> inorder (tree(baldL l a ba r)) = inorder (tree l) @ a # inorder r"
by (auto split: splits)

lemma inorder_baldR:
  "\<lbrakk> ba = Lh \<longrightarrow> l \<noteq> Leaf; avl l \<rbrakk>
   \<Longrightarrow> inorder (tree(baldR l a ba r)) = inorder l @ a # inorder (tree r)"
by (auto split: splits)

lemma avl_split_max:
  "\<lbrakk> split_max t = (t',a); avl t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> case t' of
   Same t' \<Rightarrow> avl t' \<and> height t = height t' |
   Diff t' \<Rightarrow> avl t' \<and> height t = height t' + 1"
apply(induction t arbitrary: t' a rule: split_max_induct)
 apply(fastforce simp: max_absorb1 max_absorb2 split!: splits prod.splits)
apply simp
done

lemma avl_delete_case: "avl t \<Longrightarrow> case delete x t of
   Same t' \<Rightarrow> avl t' \<and> height t = height t' |
   Diff t' \<Rightarrow> avl t' \<and> height t = height t' + 1"
apply(induction x t rule: delete.induct)
 apply(auto simp: max_absorb1 max_absorb2 dest: avl_split_max split!: splits prod.splits)
done

corollary avl_delete: "avl t \<Longrightarrow> avl(tree(delete x t))"
using avl_delete_case[of t x] by(simp split: splits)

lemma inorder_split_maxD:
  "\<lbrakk> split_max t = (t',a); t \<noteq> Leaf; avl t \<rbrakk> \<Longrightarrow>
   inorder (tree t') @ [a] = inorder t"
apply(induction t arbitrary: t' rule: split_max.induct)
 apply(fastforce split!: splits prod.splits)
apply simp
done

lemma neq_Leaf_if_height_neq_0[simp]: "height t \<noteq> 0 \<Longrightarrow> t \<noteq> Leaf"
by auto

theorem inorder_delete:
  "\<lbrakk> avl t; sorted(inorder t) \<rbrakk>  \<Longrightarrow> inorder (tree(delete x t)) = del_list x (inorder t)"
apply(induction t rule: tree2_induct)
apply(auto simp: del_list_simps inorder_baldL inorder_baldR avl_delete inorder_split_maxD
           simp del: baldR.simps baldL.simps split!: splits prod.splits)
done


subsubsection \<open>Set Implementation\<close>

interpretation S: Set_by_Ordered
where empty = Leaf and isin = isin
  and insert = "\<lambda>x t. tree(insert x t)"
  and delete = "\<lambda>x t. tree(delete x t)"
  and inorder = inorder and inv = avl
proof (standard, goal_cases)
  case 1 show ?case by (simp)
next
  case 2 thus ?case by(simp add: isin_set_inorder)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp add: empty_def)
next
  case 6 thus ?case by (simp add: avl_insert)
next
  case 7 thus ?case by (simp add: avl_delete)
qed

end
