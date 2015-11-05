(*
Author:     Tobias Nipkow
Derived from AFP entry AVL.
*)

section "AVL Tree Implementation of Sets"

theory AVL_Set
imports Cmp Isin2
begin

type_synonym 'a avl_tree = "('a,nat) tree"

text {* Invariant: *}

fun avl :: "'a avl_tree \<Rightarrow> bool" where
"avl Leaf = True" |
"avl (Node h l a r) =
 ((height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

fun ht :: "'a avl_tree \<Rightarrow> nat" where
"ht Leaf = 0" |
"ht (Node h l a r) = h"

definition node :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"node l a r = Node (max (ht l) (ht r) + 1) l a r"

definition balL :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"balL l a r = (
  if ht l = ht r + 2 then (case l of 
    Node _ bl b br \<Rightarrow> (if ht bl < ht br
    then case br of
      Node _ cl c cr \<Rightarrow> node (node bl b cl) c (node cr a r)
    else node bl b (node br a r)))
  else node l a r)"

definition balR :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"balR l a r = (
  if ht r = ht l + 2 then (case r of
    Node _ bl b br \<Rightarrow> (if ht bl > ht br
    then case bl of
      Node _ cl c cr \<Rightarrow> node (node l a cl) c (node cr b br)
    else node (node l a bl) b br))
  else node l a r)"

fun insert :: "'a::cmp \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"insert x Leaf = Node 1 Leaf x Leaf" |
"insert x (Node h l a r) = (case cmp x a of
   EQ \<Rightarrow> Node h l a r |
   LT \<Rightarrow> balL (insert x l) a r |
   GT \<Rightarrow> balR l a (insert x r))"

fun delete_max :: "'a avl_tree \<Rightarrow> 'a avl_tree * 'a" where
"delete_max (Node _ l a Leaf) = (l,a)" |
"delete_max (Node _ l a r) =
  (let (r',a') = delete_max r in (balL l a r', a'))"

lemmas delete_max_induct = delete_max.induct[case_names Leaf Node]

fun delete_root :: "'a avl_tree \<Rightarrow> 'a avl_tree" where
"delete_root (Node h Leaf a r) = r" |
"delete_root (Node h l a Leaf) = l" |
"delete_root (Node h l a r) =
  (let (l', a') = delete_max l in balR l' a' r)"

lemmas delete_root_cases = delete_root.cases[case_names Leaf_t Node_Leaf Node_Node]

fun delete :: "'a::cmp \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node h l a r) = (case cmp x a of
   EQ \<Rightarrow> delete_root (Node h l a r) |
   LT \<Rightarrow> balR (delete x l) a r |
   GT \<Rightarrow> balL l a (delete x r))"


subsection {* Functional Correctness Proofs *}

text{* Very different from the AFP/AVL proofs *}


subsubsection "Proofs for insert"

lemma inorder_balL:
  "inorder (balL l a r) = inorder l @ a # inorder r"
by (auto simp: node_def balL_def split:tree.splits)

lemma inorder_balR:
  "inorder (balR l a r) = inorder l @ a # inorder r"
by (auto simp: node_def balR_def split:tree.splits)

theorem inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (induct t) 
   (auto simp: ins_list_simps inorder_balL inorder_balR)


subsubsection "Proofs for delete"

lemma inorder_delete_maxD:
  "\<lbrakk> delete_max t = (t',a); t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   inorder t' @ [a] = inorder t"
by(induction t arbitrary: t' rule: delete_max.induct)
  (auto simp: inorder_balL split: prod.splits tree.split)

lemma inorder_delete_root:
  "inorder (delete_root (Node h l a r)) = inorder l @ inorder r"
by(induction "Node h l a r" arbitrary: l a r h rule: delete_root.induct)
  (auto simp: inorder_balR inorder_delete_maxD split: prod.splits)

theorem inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR
    inorder_delete_root inorder_delete_maxD split: prod.splits)


subsubsection "Overall functional correctness"

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and wf = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (rule TrueI)+


subsection {* AVL invariants *}

text{* Essentially the AFP/AVL proofs *}


subsubsection {* Insertion maintains AVL balance *}

declare Let_def [simp]

lemma [simp]: "avl t \<Longrightarrow> ht t = height t"
by (induct t) simp_all

lemma height_balL:
  "\<lbrakk> height l = height r + 2; avl l; avl r \<rbrakk> \<Longrightarrow>
   height (balL l a r) = height r + 2 \<or>
   height (balL l a r) = height r + 3"
by (cases l) (auto simp:node_def balL_def split:tree.split)
       
lemma height_balR:
  "\<lbrakk> height r = height l + 2; avl l; avl r \<rbrakk> \<Longrightarrow>
   height (balR l a r) = height l + 2 \<or>
   height (balR l a r) = height l + 3"
by (cases r) (auto simp add:node_def balR_def split:tree.split)

lemma [simp]: "height(node l a r) = max (height l) (height r) + 1"
by (simp add: node_def)

lemma avl_node:
  "\<lbrakk> avl l; avl r;
     height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1
   \<rbrakk> \<Longrightarrow> avl(node l a r)"
by (auto simp add:max_def node_def)

lemma height_balL2:
  "\<lbrakk> avl l; avl r; height l \<noteq> height r + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) = (1 + max (height l) (height r))"
by (cases l, cases r) (simp_all add: balL_def)

lemma height_balR2:
  "\<lbrakk> avl l;  avl r;  height r \<noteq> height l + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) = (1 + max (height l) (height r))"
by (cases l, cases r) (simp_all add: balR_def)

lemma avl_balL: 
  assumes "avl l" "avl r" and "height l = height r \<or> height l = height r + 1
    \<or> height r = height l + 1 \<or> height l = height r + 2" 
  shows "avl(balL l a r)"
proof(cases l)
  case Leaf
  with assms show ?thesis by (simp add: node_def balL_def)
next
  case (Node ln ll lr lh)
  with assms show ?thesis
  proof(cases "height l = height r + 2")
    case True
    from True Node assms show ?thesis
      by (auto simp: balL_def intro!: avl_node split: tree.split) arith+
  next
    case False
    with assms show ?thesis by (simp add: avl_node balL_def)
  qed
qed

lemma avl_balR: 
  assumes "avl l" and "avl r" and "height l = height r \<or> height l = height r + 1
    \<or> height r = height l + 1 \<or> height r = height l + 2" 
  shows "avl(balR l a r)"
proof(cases r)
  case Leaf
  with assms show ?thesis by (simp add: node_def balR_def)
next
  case (Node rn rl rr rh)
  with assms show ?thesis
  proof(cases "height r = height l + 2")
    case True
      from True Node assms show ?thesis
        by (auto simp: balR_def intro!: avl_node split: tree.split) arith+
  next
    case False
    with assms show ?thesis by (simp add: balR_def avl_node)
  qed
qed

(* It appears that these two properties need to be proved simultaneously: *)

text{* Insertion maintains the AVL property: *}

theorem avl_insert_aux:
  assumes "avl t"
  shows "avl(insert x t)"
        "(height (insert x t) = height t \<or> height (insert x t) = height t + 1)"
using assms
proof (induction t)
  case (Node h l a r)
  case 1
  with Node show ?case
  proof(cases "x = a")
    case True
    with Node 1 show ?thesis by simp
  next
    case False
    with Node 1 show ?thesis 
    proof(cases "x<a")
      case True
      with Node 1 show ?thesis by (auto simp add:avl_balL)
    next
      case False
      with Node 1 `x\<noteq>a` show ?thesis by (auto simp add:avl_balR)
    qed
  qed
  case 2
  from 2 Node show ?case
  proof(cases "x = a")
    case True
    with Node 1 show ?thesis by simp
  next
    case False
    with Node 1 show ?thesis 
     proof(cases "x<a")
      case True
      with Node 2 show ?thesis
      proof(cases "height (insert x l) = height r + 2")
        case False with Node 2 `x < a` show ?thesis by (auto simp: height_balL2)
      next
        case True 
        hence "(height (balL (insert x l) a r) = height r + 2) \<or>
          (height (balL (insert x l) a r) = height r + 3)" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) simp_all
        thus ?thesis
        proof
          assume ?A
          with 2 `x < a` show ?thesis by (auto)
        next
          assume ?B
          with True 1 Node(2) `x < a` show ?thesis by (simp) arith
        qed
      qed
    next
      case False
      with Node 2 show ?thesis 
      proof(cases "height (insert x r) = height l + 2")
        case False
        with Node 2 `\<not>x < a` show ?thesis by (auto simp: height_balR2)
      next
        case True 
        hence "(height (balR l a (insert x r)) = height l + 2) \<or>
          (height (balR l a (insert x r)) = height l + 3)"  (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) simp_all
        thus ?thesis 
        proof
          assume ?A
          with 2 `\<not>x < a` show ?thesis by (auto)
        next
          assume ?B
          with True 1 Node(4) `\<not>x < a` show ?thesis by (simp) arith
        qed
      qed
    qed
  qed
qed simp_all


subsubsection {* Deletion maintains AVL balance *}

lemma avl_delete_max:
  assumes "avl x" and "x \<noteq> Leaf"
  shows "avl (fst (delete_max x))" "height x = height(fst (delete_max x)) \<or>
         height x = height(fst (delete_max x)) + 1"
using assms
proof (induct x rule: delete_max_induct)
  case (Node h l a rh rl b rr)
  case 1
  with Node have "avl l" "avl (fst (delete_max (Node rh rl b rr)))" by auto
  with 1 Node have "avl (balL l a (fst (delete_max (Node rh rl b rr))))"
    by (intro avl_balL) fastforce+
  thus ?case 
    by (auto simp: height_balL height_balL2
      linorder_class.max.absorb1 linorder_class.max.absorb2
      split:prod.split)
next
  case (Node h l a rh rl b rr)
  case 2
  let ?r = "Node rh rl b rr"
  let ?r' = "fst (delete_max ?r)"
  from `avl x` Node 2 have "avl l" and "avl ?r" by simp_all
  thus ?case using Node 2 height_balL[of l ?r' a] height_balL2[of l ?r' a]
    apply (auto split:prod.splits simp del:avl.simps) by arith+
qed auto

lemma avl_delete_root:
  assumes "avl t" and "t \<noteq> Leaf"
  shows "avl(delete_root t)" 
using assms
proof (cases t rule:delete_root_cases)
  case (Node_Node h lh ll ln lr n rh rl rn rr)
  let ?l = "Node lh ll ln lr"
  let ?r = "Node rh rl rn rr"
  let ?l' = "fst (delete_max ?l)"
  from `avl t` and Node_Node have "avl ?r" by simp
  from `avl t` and Node_Node have "avl ?l" by simp
  hence "avl(?l')" "height ?l = height(?l') \<or>
         height ?l = height(?l') + 1" by (rule avl_delete_max,simp)+
  with `avl t` Node_Node have "height ?l' = height ?r \<or> height ?l' = height ?r + 1
            \<or> height ?r = height ?l' + 1 \<or> height ?r = height ?l' + 2" by fastforce
  with `avl ?l'` `avl ?r` have "avl(balR ?l' (snd(delete_max ?l)) ?r)"
    by (rule avl_balR)
  with Node_Node show ?thesis by (auto split:prod.splits)
qed simp_all

lemma height_delete_root:
  assumes "avl t" and "t \<noteq> Leaf" 
  shows "height t = height(delete_root t) \<or> height t = height(delete_root t) + 1"
using assms
proof (cases t rule: delete_root_cases)
  case (Node_Node h lh ll ln lr n rh rl rn rr)
  let ?l = "Node lh ll ln lr"
  let ?r = "Node rh rl rn rr"
  let ?l' = "fst (delete_max ?l)"
  let ?t' = "balR ?l' (snd(delete_max ?l)) ?r"
  from `avl t` and Node_Node have "avl ?r" by simp
  from `avl t` and Node_Node have "avl ?l" by simp
  hence "avl(?l')"  by (rule avl_delete_max,simp)
  have l'_height: "height ?l = height ?l' \<or> height ?l = height ?l' + 1" using `avl ?l` by (intro avl_delete_max) auto
  have t_height: "height t = 1 + max (height ?l) (height ?r)" using `avl t` Node_Node by simp
  have "height t = height ?t' \<or> height t = height ?t' + 1" using  `avl t` Node_Node
  proof(cases "height ?r = height ?l' + 2")
    case False
    show ?thesis using l'_height t_height False by (subst  height_balR2[OF `avl ?l'` `avl ?r` False])+ arith
  next
    case True
    show ?thesis
    proof(cases rule: disjE[OF height_balR[OF True `avl ?l'` `avl ?r`, of "snd (delete_max ?l)"]])
      case 1
      thus ?thesis using l'_height t_height True by arith
    next
      case 2
      thus ?thesis using l'_height t_height True by arith
    qed
  qed
  thus ?thesis using Node_Node by (auto split:prod.splits)
qed simp_all

text{* Deletion maintains the AVL property: *}

theorem avl_delete_aux:
  assumes "avl t" 
  shows "avl(delete x t)" and "height t = (height (delete x t)) \<or> height t = height (delete x t) + 1"
using assms
proof (induct t)
  case (Node h l n r)
  case 1
  with Node show ?case
  proof(cases "x = n")
    case True
    with Node 1 show ?thesis by (auto simp:avl_delete_root)
  next
    case False
    with Node 1 show ?thesis 
    proof(cases "x<n")
      case True
      with Node 1 show ?thesis by (auto simp add:avl_balR)
    next
      case False
      with Node 1 `x\<noteq>n` show ?thesis by (auto simp add:avl_balL)
    qed
  qed
  case 2
  with Node show ?case
  proof(cases "x = n")
    case True
    with 1 have "height (Node h l n r) = height(delete_root (Node h l n r))
      \<or> height (Node h l n r) = height(delete_root (Node h l n r)) + 1"
      by (subst height_delete_root,simp_all)
    with True show ?thesis by simp
  next
    case False
    with Node 1 show ?thesis 
     proof(cases "x<n")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + 2")
        case False with Node 1 `x < n` show ?thesis by(auto simp: balR_def)
      next
        case True 
        hence "(height (balR (delete x l) n r) = height (delete x l) + 2) \<or>
          height (balR (delete x l) n r) = height (delete x l) + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) auto
        thus ?thesis 
        proof
          assume ?A
          with `x < n` Node 2 show ?thesis by(auto simp: balR_def)
        next
          assume ?B
          with `x < n` Node 2 show ?thesis by(auto simp: balR_def)
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + 2")
        case False with Node 1 `\<not>x < n` `x \<noteq> n` show ?thesis by(auto simp: balL_def)
      next
        case True 
        hence "(height (balL l n (delete x r)) = height (delete x r) + 2) \<or>
          height (balL l n (delete x r)) = height (delete x r) + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) auto
        thus ?thesis 
        proof
          assume ?A
          with `\<not>x < n` `x \<noteq> n` Node 2 show ?thesis by(auto simp: balL_def)
        next
          assume ?B
          with `\<not>x < n` `x \<noteq> n` Node 2 show ?thesis by(auto simp: balL_def)
        qed
      qed
    qed
  qed
qed simp_all

end
