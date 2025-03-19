(* Author: Tobias Nipkow *)

section "AVL Tree with Balance Factors (2)"

theory AVL_Bal2_Set
imports
  Cmp
  Isin2
begin

text \<open>This version passes a flag (\<open>Same\<close>/\<open>Diff\<close>) back up to signal if the height changed.\<close>

datatype bal = Lh | Bal | Rh

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

datatype 'a alt = Same 'a | Diff 'a

type_synonym 'a tree_bal2 = "'a tree_bal alt"

fun tree :: "'a alt \<Rightarrow> 'a" where
"tree(Same t) = t" |
"tree(Diff t) = t"

fun rot2 where
"rot2 A a B c C = (case B of
  (Node B\<^sub>1 (b, bb) B\<^sub>2) \<Rightarrow>
    let b\<^sub>1 = if bb = Rh then Lh else Bal;
        b\<^sub>2 = if bb = Lh then Rh else Bal
    in Node (Node A (a,b\<^sub>1) B\<^sub>1) (b,Bal) (Node B\<^sub>2 (c,b\<^sub>2) C))"

fun balL :: "'a tree_bal2 \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal2" where
"balL AB' c bc C = (case AB' of
   Same AB \<Rightarrow> Same (Node AB (c,bc) C) |
   Diff AB \<Rightarrow> (case bc of
     Bal \<Rightarrow> Diff (Node AB (c,Lh) C) |
     Rh \<Rightarrow> Same (Node AB (c,Bal) C) |
     Lh \<Rightarrow> (case AB of
       Node A (a,Lh) B \<Rightarrow> Same(Node A (a,Bal) (Node B (c,Bal) C)) |
       Node A (a,Rh) B \<Rightarrow> Same(rot2 A a B c C))))"

fun balR :: "'a tree_bal \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal2 \<Rightarrow> 'a tree_bal2" where
"balR A a ba BC' = (case BC' of
   Same BC \<Rightarrow> Same (Node A (a,ba) BC) |
   Diff BC \<Rightarrow> (case ba of
     Bal \<Rightarrow> Diff (Node A (a,Rh) BC) |
     Lh \<Rightarrow> Same (Node A (a,Bal) BC) |
     Rh \<Rightarrow> (case BC of
       Node B (c,Rh) C \<Rightarrow> Same(Node (Node A (a,Bal) B) (c,Bal) C) |
       Node B (c,Lh) C \<Rightarrow> Same(rot2 A a B c C))))"

fun ins :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal2" where
"ins x Leaf = Diff(Node Leaf (x, Bal) Leaf)" |
"ins x (Node l (a, b) r) = (case cmp x a of
   EQ \<Rightarrow> Same(Node l (a, b) r) |
   LT \<Rightarrow> balL (ins x l) a b r |
   GT \<Rightarrow> balR l a b (ins x r))"

definition insert :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal" where
"insert x t = tree(ins x t)"

fun baldR :: "'a tree_bal \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal2 \<Rightarrow> 'a tree_bal2" where
"baldR AB c bc C' = (case C' of
   Same C \<Rightarrow> Same (Node AB (c,bc) C) |
   Diff C \<Rightarrow> (case bc of
     Bal \<Rightarrow> Same (Node AB (c,Lh) C) |
     Rh \<Rightarrow> Diff (Node AB (c,Bal) C) |
     Lh \<Rightarrow> (case AB of
       Node A (a,Lh) B \<Rightarrow> Diff(Node A (a,Bal) (Node B (c,Bal) C)) |
       Node A (a,Bal) B \<Rightarrow> Same(Node A (a,Rh) (Node B (c,Lh) C)) |
       Node A (a,Rh) B \<Rightarrow> Diff(rot2 A a B c C))))"

fun baldL :: "'a tree_bal2 \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal2" where
"baldL A' a ba BC = (case A' of
   Same A \<Rightarrow> Same (Node A (a,ba) BC) |
   Diff A \<Rightarrow> (case ba of
     Bal \<Rightarrow> Same (Node A (a,Rh) BC) |
     Lh \<Rightarrow> Diff (Node A (a,Bal) BC) |
     Rh \<Rightarrow> (case BC of
       Node B (c,Rh) C \<Rightarrow> Diff(Node (Node A (a,Bal) B) (c,Bal) C) |
       Node B (c,Bal) C \<Rightarrow> Same(Node (Node A (a,Rh) B) (c,Lh) C) |
       Node B (c,Lh) C \<Rightarrow> Diff(rot2 A a B c C))))"

fun split_max :: "'a tree_bal \<Rightarrow> 'a tree_bal2 * 'a" where
"split_max (Node l (a, ba) r) =
  (if r = Leaf then (Diff l,a) else let (r',a') = split_max r in (baldR l a ba r', a'))"

fun del :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal2" where
"del _ Leaf = Same Leaf" |
"del x (Node l (a, ba) r) =
  (case cmp x a of
     EQ \<Rightarrow> if l = Leaf then Diff r
           else let (l', a') = split_max l in baldL l' a' ba r |
     LT \<Rightarrow> baldL (del x l) a ba r |
     GT \<Rightarrow> baldR l a ba (del x r))"

definition delete :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal" where
"delete x t = tree(del x t)"

lemmas split_max_induct = split_max.induct[case_names Node Leaf]

lemmas splits = if_splits tree.splits alt.splits bal.splits

subsection \<open>Proofs\<close>

subsubsection "Proofs about insertion"

lemma avl_ins_case: "avl t \<Longrightarrow> case ins x t of
   Same t' \<Rightarrow> avl t' \<and> height t' = height t |
   Diff t' \<Rightarrow> avl t' \<and> height t' = height t + 1 \<and>
      (\<forall>l a r. t' = Node l (a,Bal) r \<longrightarrow> a = x \<and> l = Leaf \<and> r = Leaf)"
  by (induction x t rule: ins.induct) (auto simp: max_absorb1 split!: splits)

corollary avl_insert: "avl t \<Longrightarrow> avl(insert x t)"
using avl_ins_case[of t x] by (simp add: insert_def split: splits)

(* The following aux lemma simplifies the inorder_ins proof *)

lemma ins_Diff[simp]: "avl t \<Longrightarrow>
  ins x t \<noteq> Diff Leaf \<and>
  (ins x t = Diff (Node l (a,Bal) r) \<longleftrightarrow> t = Leaf \<and> a = x \<and> l=Leaf \<and> r=Leaf) \<and>
  ins x t \<noteq> Diff (Node l (a,Rh) Leaf) \<and>
  ins x t \<noteq> Diff (Node Leaf (a,Lh) r)"
by(drule avl_ins_case[of _ x]) (auto split: splits)

theorem inorder_ins:
  "\<lbrakk> avl t;  sorted(inorder t) \<rbrakk> \<Longrightarrow> inorder(tree(ins x t)) = ins_list x (inorder t)"
  by (induction t) (auto simp: ins_list_simps  split!: splits)


subsubsection "Proofs about deletion"

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
proof (induction t arbitrary: t' a rule: split_max_induct)
qed (auto simp: max_def split!: splits prod.splits)

lemma avl_del_case: "avl t \<Longrightarrow> case del x t of
   Same t' \<Rightarrow> avl t' \<and> height t = height t' |
   Diff t' \<Rightarrow> avl t' \<and> height t = height t' + 1"
proof (induction x t rule: del.induct)
qed (auto simp: max_absorb1 max_absorb2 dest: avl_split_max split!: splits prod.splits)

corollary avl_delete: "avl t \<Longrightarrow> avl(delete x t)"
using avl_del_case[of t x] by(simp add: delete_def split: splits)

lemma inorder_split_maxD:
  "\<lbrakk> split_max t = (t',a); t \<noteq> Leaf; avl t \<rbrakk> \<Longrightarrow>
   inorder (tree t') @ [a] = inorder t"
proof (induction t arbitrary: t' rule: split_max.induct)
qed (auto  split!: splits prod.splits)

lemma neq_Leaf_if_height_neq_0[simp]: "height t \<noteq> 0 \<Longrightarrow> t \<noteq> Leaf"
by auto

theorem inorder_del:
  "\<lbrakk> avl t; sorted(inorder t) \<rbrakk>  \<Longrightarrow> inorder (tree(del x t)) = del_list x (inorder t)"
proof (induction t rule: tree2_induct)
  case Leaf
  then show ?case by simp
next
  case (Node x1 a b x3)
  then show ?case 
    by (auto simp: del_list_simps inorder_baldL inorder_baldR avl_delete inorder_split_maxD
           simp del:  baldL.simps split!: splits prod.splits)
qed


subsubsection \<open>Set Implementation\<close>

interpretation S: Set_by_Ordered
where empty = Leaf and isin = isin
  and insert = insert
  and delete = delete
  and inorder = inorder and inv = avl
proof (standard, goal_cases)
  case 1 show ?case by (simp)
next
  case 2 thus ?case by(simp add: isin_set_inorder)
next
  case 3 thus ?case by(simp add: inorder_ins insert_def)
next
  case 4 thus ?case by(simp add: inorder_del delete_def)
next
  case 5 thus ?case by (simp)
next
  case 6 thus ?case by (simp add: avl_insert)
next
  case 7 thus ?case by (simp add: avl_delete)
qed

end
