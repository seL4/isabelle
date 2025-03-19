(* Author: Tobias Nipkow *)

section "AVL Tree with Balance Factors (1)"

theory AVL_Bal_Set
imports
  Cmp
  Isin2
begin

text \<open>This version detects height increase/decrease from above via the change in balance factors.\<close>

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

fun is_bal where
"is_bal (Node l (a,b) r) = (b = Bal)"

fun incr where
"incr t t' = (t = Leaf \<or> is_bal t \<and> \<not> is_bal t')"

fun rot2 where
"rot2 A a B c C = (case B of
  (Node B\<^sub>1 (b, bb) B\<^sub>2) \<Rightarrow>
    let b\<^sub>1 = if bb = Rh then Lh else Bal;
        b\<^sub>2 = if bb = Lh then Rh else Bal
    in Node (Node A (a,b\<^sub>1) B\<^sub>1) (b,Bal) (Node B\<^sub>2 (c,b\<^sub>2) C))"

fun balL :: "'a tree_bal \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal" where
"balL AB c bc C = (case bc of
     Bal \<Rightarrow> Node AB (c,Lh) C |
     Rh \<Rightarrow> Node AB (c,Bal) C |
     Lh \<Rightarrow> (case AB of
       Node A (a,Lh) B \<Rightarrow> Node A (a,Bal) (Node B (c,Bal) C) |
       Node A (a,Bal) B \<Rightarrow> Node A (a,Rh) (Node B (c,Lh) C) |
       Node A (a,Rh) B \<Rightarrow> rot2 A a B c C))"

fun balR :: "'a tree_bal \<Rightarrow> 'a \<Rightarrow> bal \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal" where
"balR A a ba BC = (case ba of
     Bal \<Rightarrow> Node A (a,Rh) BC |
     Lh \<Rightarrow> Node A (a,Bal) BC |
     Rh \<Rightarrow> (case BC of
       Node B (c,Rh) C \<Rightarrow> Node (Node A (a,Bal) B) (c,Bal) C |
       Node B (c,Bal) C \<Rightarrow> Node (Node A (a,Rh) B) (c,Lh) C |
       Node B (c,Lh) C \<Rightarrow> rot2 A a B c C))"

fun insert :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal" where
"insert x Leaf = Node Leaf (x, Bal) Leaf" |
"insert x (Node l (a, b) r) = (case cmp x a of
   EQ \<Rightarrow> Node l (a, b) r |
   LT \<Rightarrow> let l' = insert x l in if incr l l' then balL l' a b r else Node l' (a,b) r |
   GT \<Rightarrow> let r' = insert x r in if incr r r' then balR l a b r' else Node l (a,b) r')"

fun decr where
"decr t t' = (t \<noteq> Leaf \<and> incr t' t)"

fun split_max :: "'a tree_bal \<Rightarrow> 'a tree_bal * 'a" where
"split_max (Node l (a, ba) r) =
  (if r = Leaf then (l,a)
   else let (r',a') = split_max r;
            t' = if incr r' r then balL l a ba r' else Node l (a,ba) r'
        in (t', a'))"

fun delete :: "'a::linorder \<Rightarrow> 'a tree_bal \<Rightarrow> 'a tree_bal" where
"delete _ Leaf = Leaf" |
"delete x (Node l (a, ba) r) =
  (case cmp x a of
     EQ \<Rightarrow> if l = Leaf then r
           else let (l', a') = split_max l in
                if incr l' l then balR l' a' ba r else Node l' (a',ba) r |
     LT \<Rightarrow> let l' = delete x l in if decr l l' then balR l' a ba r else Node l' (a,ba) r |
     GT \<Rightarrow> let r' = delete x r in if decr r r' then balL l a ba r' else Node l (a,ba) r')"


subsection \<open>Proofs\<close>

lemmas split_max_induct = split_max.induct[case_names Node Leaf]

lemmas splits = if_splits tree.splits bal.splits

declare Let_def [simp]

subsubsection "Proofs about insertion"

lemma avl_insert: "avl t \<Longrightarrow>
  avl(insert x t) \<and>
  height(insert x t) = height t + (if incr t (insert x t) then 1 else 0)"
  by (induction x t rule: insert.induct)(auto split!: splits)

text \<open>The following two auxiliary lemma merely simplify the proof of \<open>inorder_insert\<close>.\<close>

lemma [simp]: "[] \<noteq> ins_list x xs"
by(cases xs) auto

lemma [simp]: "avl t \<Longrightarrow> insert x t \<noteq> \<langle>l, (a, Rh), \<langle>\<rangle>\<rangle> \<and> insert x t \<noteq> \<langle>\<langle>\<rangle>, (a, Lh), r\<rangle>"
by(drule avl_insert[of _ x]) (auto split: splits)

theorem inorder_insert:
  "\<lbrakk> avl t;  sorted(inorder t) \<rbrakk> \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
  by (induction t) (auto simp: ins_list_simps split!: splits)


subsubsection "Proofs about deletion"

lemma inorder_balR:
  "\<lbrakk> ba = Rh \<longrightarrow> r \<noteq> Leaf; avl r \<rbrakk>
  \<Longrightarrow> inorder (balR l a ba r) = inorder l @ a # inorder r"
by (auto split: splits)

lemma inorder_balL:
  "\<lbrakk> ba = Lh \<longrightarrow> l \<noteq> Leaf; avl l \<rbrakk>
   \<Longrightarrow> inorder (balL l a ba r) = inorder l @ a # inorder r"
by (auto split: splits)

lemma height_1_iff: "avl t \<Longrightarrow> height t = Suc 0 \<longleftrightarrow> (\<exists>x. t = Node Leaf (x,Bal) Leaf)"
by(cases t) (auto split: splits prod.splits)

lemma avl_split_max:
  "\<lbrakk> split_max t = (t',a); avl t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   avl t' \<and> height t = height t' + (if incr t' t then 1 else 0)"
proof (induction t arbitrary: t' a rule: split_max_induct)
qed (auto simp: max_absorb1 max_absorb2 height_1_iff split!: splits prod.splits)

lemma avl_delete: "avl t \<Longrightarrow>
  avl (delete x t) \<and>
  height t = height (delete x t) + (if decr t (delete x t) then 1 else 0)"
proof (induction x t rule: delete.induct)
qed (auto simp: max_absorb1 max_absorb2 height_1_iff dest: avl_split_max split!: splits prod.splits)

lemma inorder_split_maxD:
  "\<lbrakk> split_max t = (t',a); t \<noteq> Leaf; avl t \<rbrakk> \<Longrightarrow>
   inorder t' @ [a] = inorder t"
proof (induction t arbitrary: t' rule: split_max.induct)
qed (auto split!: splits prod.splits)

lemma neq_Leaf_if_height_neq_0: "height t \<noteq> 0 \<Longrightarrow> t \<noteq> Leaf"
by auto

lemma split_max_Leaf: "\<lbrakk> t \<noteq> Leaf; avl t \<rbrakk> \<Longrightarrow> split_max t = (\<langle>\<rangle>, x) \<longleftrightarrow> t = Node Leaf (x,Bal) Leaf"
by(cases t) (auto split: splits prod.splits)

theorem inorder_delete:
  "\<lbrakk> avl t; sorted(inorder t) \<rbrakk>  \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
proof (induction t rule: tree2_induct)
  case Leaf
  then show ?case by auto
next
  case (Node x1 a b x3)
  then show ?case 
    by (auto simp: del_list_simps inorder_balR inorder_balL avl_delete inorder_split_maxD
                   split_max_Leaf neq_Leaf_if_height_neq_0
         simp del: balL.simps balR.simps split!: splits prod.splits)
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
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp)
next
  case 6 thus ?case by (simp add: avl_insert)
next
  case 7 thus ?case by (simp add: avl_delete)
qed

end
