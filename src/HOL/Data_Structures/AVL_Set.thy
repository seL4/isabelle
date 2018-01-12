(*
Author:     Tobias Nipkow, Daniel Stüwe
Largely derived from AFP entry AVL.
*)

section "AVL Tree Implementation of Sets"

theory AVL_Set
imports
 Cmp
 Isin2
  "HOL-Number_Theory.Fib"
begin

type_synonym 'a avl_tree = "('a,nat) tree"

text \<open>Invariant:\<close>

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
"balL l a r =
  (if ht l = ht r + 2 then
     case l of 
       Node _ bl b br \<Rightarrow>
         if ht bl < ht br then
           case br of
             Node _ cl c cr \<Rightarrow> node (node bl b cl) c (node cr a r)
         else node bl b (node br a r)
   else node l a r)"

definition balR :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"balR l a r =
   (if ht r = ht l + 2 then
      case r of
        Node _ bl b br \<Rightarrow>
          if ht bl > ht br then
            case bl of
              Node _ cl c cr \<Rightarrow> node (node l a cl) c (node cr b br)
          else node (node l a bl) b br
  else node l a r)"

fun insert :: "'a::linorder \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"insert x Leaf = Node 1 Leaf x Leaf" |
"insert x (Node h l a r) = (case cmp x a of
   EQ \<Rightarrow> Node h l a r |
   LT \<Rightarrow> balL (insert x l) a r |
   GT \<Rightarrow> balR l a (insert x r))"

fun del_max :: "'a avl_tree \<Rightarrow> 'a avl_tree * 'a" where
"del_max (Node _ l a r) =
  (if r = Leaf then (l,a) else let (r',a') = del_max r in (balL l a r', a'))"

lemmas del_max_induct = del_max.induct[case_names Node Leaf]

fun del_root :: "'a avl_tree \<Rightarrow> 'a avl_tree" where
"del_root (Node h Leaf a r) = r" |
"del_root (Node h l a Leaf) = l" |
"del_root (Node h l a r) = (let (l', a') = del_max l in balR l' a' r)"

lemmas del_root_cases = del_root.cases[case_names Leaf_t Node_Leaf Node_Node]

fun delete :: "'a::linorder \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node h l a r) =
  (case cmp x a of
     EQ \<Rightarrow> del_root (Node h l a r) |
     LT \<Rightarrow> balR (delete x l) a r |
     GT \<Rightarrow> balL l a (delete x r))"


subsection \<open>Functional Correctness Proofs\<close>

text\<open>Very different from the AFP/AVL proofs\<close>


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

lemma inorder_del_maxD:
  "\<lbrakk> del_max t = (t',a); t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   inorder t' @ [a] = inorder t"
by(induction t arbitrary: t' rule: del_max.induct)
  (auto simp: inorder_balL split: if_splits prod.splits tree.split)

lemma inorder_del_root:
  "inorder (del_root (Node h l a r)) = inorder l @ inorder r"
by(cases "Node h l a r" rule: del_root.cases)
  (auto simp: inorder_balL inorder_balR inorder_del_maxD split: if_splits prod.splits)

theorem inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR
    inorder_del_root inorder_del_maxD split: prod.splits)


subsubsection "Overall functional correctness"

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (rule TrueI)+


subsection \<open>AVL invariants\<close>

text\<open>Essentially the AFP/AVL proofs\<close>


subsubsection \<open>Insertion maintains AVL balance\<close>

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

text\<open>Insertion maintains the AVL property:\<close>

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
      with Node 1 \<open>x\<noteq>a\<close> show ?thesis by (auto simp add:avl_balR)
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
        case False with Node 2 \<open>x < a\<close> show ?thesis by (auto simp: height_balL2)
      next
        case True 
        hence "(height (balL (insert x l) a r) = height r + 2) \<or>
          (height (balL (insert x l) a r) = height r + 3)" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) simp_all
        thus ?thesis
        proof
          assume ?A
          with 2 \<open>x < a\<close> show ?thesis by (auto)
        next
          assume ?B
          with True 1 Node(2) \<open>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    next
      case False
      with Node 2 show ?thesis 
      proof(cases "height (insert x r) = height l + 2")
        case False
        with Node 2 \<open>\<not>x < a\<close> show ?thesis by (auto simp: height_balR2)
      next
        case True 
        hence "(height (balR l a (insert x r)) = height l + 2) \<or>
          (height (balR l a (insert x r)) = height l + 3)"  (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) simp_all
        thus ?thesis 
        proof
          assume ?A
          with 2 \<open>\<not>x < a\<close> show ?thesis by (auto)
        next
          assume ?B
          with True 1 Node(4) \<open>\<not>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    qed
  qed
qed simp_all


subsubsection \<open>Deletion maintains AVL balance\<close>

lemma avl_del_max:
  assumes "avl x" and "x \<noteq> Leaf"
  shows "avl (fst (del_max x))" "height x = height(fst (del_max x)) \<or>
         height x = height(fst (del_max x)) + 1"
using assms
proof (induct x rule: del_max_induct)
  case (Node h l a r)
  case 1
  thus ?case using Node
    by (auto simp: height_balL height_balL2 avl_balL
      linorder_class.max.absorb1 linorder_class.max.absorb2
      split:prod.split)
next
  case (Node h l a r)
  case 2
  let ?r' = "fst (del_max r)"
  from \<open>avl x\<close> Node 2 have "avl l" and "avl r" by simp_all
  thus ?case using Node 2 height_balL[of l ?r' a] height_balL2[of l ?r' a]
    apply (auto split:prod.splits simp del:avl.simps) by arith+
qed auto

lemma avl_del_root:
  assumes "avl t" and "t \<noteq> Leaf"
  shows "avl(del_root t)" 
using assms
proof (cases t rule:del_root_cases)
  case (Node_Node h lh ll ln lr n rh rl rn rr)
  let ?l = "Node lh ll ln lr"
  let ?r = "Node rh rl rn rr"
  let ?l' = "fst (del_max ?l)"
  from \<open>avl t\<close> and Node_Node have "avl ?r" by simp
  from \<open>avl t\<close> and Node_Node have "avl ?l" by simp
  hence "avl(?l')" "height ?l = height(?l') \<or>
         height ?l = height(?l') + 1" by (rule avl_del_max,simp)+
  with \<open>avl t\<close> Node_Node have "height ?l' = height ?r \<or> height ?l' = height ?r + 1
            \<or> height ?r = height ?l' + 1 \<or> height ?r = height ?l' + 2" by fastforce
  with \<open>avl ?l'\<close> \<open>avl ?r\<close> have "avl(balR ?l' (snd(del_max ?l)) ?r)"
    by (rule avl_balR)
  with Node_Node show ?thesis by (auto split:prod.splits)
qed simp_all

lemma height_del_root:
  assumes "avl t" and "t \<noteq> Leaf" 
  shows "height t = height(del_root t) \<or> height t = height(del_root t) + 1"
using assms
proof (cases t rule: del_root_cases)
  case (Node_Node h lh ll ln lr n rh rl rn rr)
  let ?l = "Node lh ll ln lr"
  let ?r = "Node rh rl rn rr"
  let ?l' = "fst (del_max ?l)"
  let ?t' = "balR ?l' (snd(del_max ?l)) ?r"
  from \<open>avl t\<close> and Node_Node have "avl ?r" by simp
  from \<open>avl t\<close> and Node_Node have "avl ?l" by simp
  hence "avl(?l')"  by (rule avl_del_max,simp)
  have l'_height: "height ?l = height ?l' \<or> height ?l = height ?l' + 1" using \<open>avl ?l\<close> by (intro avl_del_max) auto
  have t_height: "height t = 1 + max (height ?l) (height ?r)" using \<open>avl t\<close> Node_Node by simp
  have "height t = height ?t' \<or> height t = height ?t' + 1" using  \<open>avl t\<close> Node_Node
  proof(cases "height ?r = height ?l' + 2")
    case False
    show ?thesis using l'_height t_height False by (subst  height_balR2[OF \<open>avl ?l'\<close> \<open>avl ?r\<close> False])+ arith
  next
    case True
    show ?thesis
    proof(cases rule: disjE[OF height_balR[OF True \<open>avl ?l'\<close> \<open>avl ?r\<close>, of "snd (del_max ?l)"]])
      case 1
      thus ?thesis using l'_height t_height True by arith
    next
      case 2
      thus ?thesis using l'_height t_height True by arith
    qed
  qed
  thus ?thesis using Node_Node by (auto split:prod.splits)
qed simp_all

text\<open>Deletion maintains the AVL property:\<close>

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
    with Node 1 show ?thesis by (auto simp:avl_del_root)
  next
    case False
    with Node 1 show ?thesis 
    proof(cases "x<n")
      case True
      with Node 1 show ?thesis by (auto simp add:avl_balR)
    next
      case False
      with Node 1 \<open>x\<noteq>n\<close> show ?thesis by (auto simp add:avl_balL)
    qed
  qed
  case 2
  with Node show ?case
  proof(cases "x = n")
    case True
    with 1 have "height (Node h l n r) = height(del_root (Node h l n r))
      \<or> height (Node h l n r) = height(del_root (Node h l n r)) + 1"
      by (subst height_del_root,simp_all)
    with True show ?thesis by simp
  next
    case False
    with Node 1 show ?thesis 
     proof(cases "x<n")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + 2")
        case False with Node 1 \<open>x < n\<close> show ?thesis by(auto simp: balR_def)
      next
        case True 
        hence "(height (balR (delete x l) n r) = height (delete x l) + 2) \<or>
          height (balR (delete x l) n r) = height (delete x l) + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) auto
        thus ?thesis 
        proof
          assume ?A
          with \<open>x < n\<close> Node 2 show ?thesis by(auto simp: balR_def)
        next
          assume ?B
          with \<open>x < n\<close> Node 2 show ?thesis by(auto simp: balR_def)
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + 2")
        case False with Node 1 \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> show ?thesis by(auto simp: balL_def)
      next
        case True 
        hence "(height (balL l n (delete x r)) = height (delete x r) + 2) \<or>
          height (balL l n (delete x r)) = height (delete x r) + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) auto
        thus ?thesis 
        proof
          assume ?A
          with \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> Node 2 show ?thesis by(auto simp: balL_def)
        next
          assume ?B
          with \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> Node 2 show ?thesis by(auto simp: balL_def)
        qed
      qed
    qed
  qed
qed simp_all


subsection \<open>Height-Size Relation\<close>

text \<open>By Daniel St\"uwe\<close>

fun fib_tree :: "nat \<Rightarrow> unit avl_tree" where
"fib_tree 0 = Leaf" |
"fib_tree (Suc 0) = Node 1 Leaf () Leaf" |
"fib_tree (Suc(Suc n)) = Node (Suc(Suc(n))) (fib_tree (Suc n)) () (fib_tree n)"

lemma [simp]: "ht (fib_tree h) = h"
by (induction h rule: "fib_tree.induct") auto

lemma [simp]: "height (fib_tree h) = h"
by (induction h rule: "fib_tree.induct") auto

lemma "avl(fib_tree h)"          
by (induction h rule: "fib_tree.induct") auto

lemma fib_tree_size1: "size1 (fib_tree h) = fib (h+2)"
by (induction h rule: fib_tree.induct) auto

lemma height_invers[simp]: 
  "(height t = 0) = (t = Leaf)"
  "avl t \<Longrightarrow> (height t = Suc h) = (\<exists> l a r . t = Node (Suc h) l a r)"
by (induction t) auto

lemma fib_Suc_lt: "fib n \<le> fib (Suc n)"
by (induction n rule: fib.induct) auto

lemma fib_mono: "n \<le> m \<Longrightarrow> fib n \<le> fib m"
proof (induction n arbitrary: m rule: fib.induct )
  case (2 m)
  thus ?case using fib_neq_0_nat[of m] by auto
next
  case (3 n m)
  from 3 obtain m' where "m = Suc (Suc m')"
    by (metis le_Suc_ex plus_nat.simps(2)) 
  thus ?case using 3(1)[of "Suc m'"] 3(2)[of m'] 3(3) by auto
qed simp

lemma size1_fib_tree_mono:
  assumes "n \<le> m"
  shows   "size1 (fib_tree n) \<le> size1 (fib_tree m)"
using fib_tree_size1 fib_mono[OF assms] fib_mono[of "Suc n"] add_le_mono assms by fastforce 

lemma fib_tree_minimal: "avl t \<Longrightarrow> size1 (fib_tree (ht t)) \<le> size1 t"
proof (induction "ht t" arbitrary: t rule: fib_tree.induct)
  case (2 t)
  from 2 obtain l a r where "t = Node (Suc 0) l a r" by (cases t) auto
  with 2 show ?case by auto
next
  case (3 h t)
  note [simp] = 3(3)[symmetric] 
  from 3 obtain l a r where [simp]: "t = Node (Suc (Suc h)) l a r" by (cases t) auto
  show ?case proof (cases rule: linorder_cases[of "ht l" "ht r"]) 
    case equal
    with 3(3,4) have ht: "ht l = Suc h" "ht r = Suc h" by auto
    with 3 have "size1 (fib_tree (ht l)) \<le> size1 l" by auto moreover
    from 3(1)[of r] 3(3,4) ht(2) have "size1 (fib_tree (ht r)) \<le> size1 r" by auto ultimately
    show ?thesis using ht size1_fib_tree_mono[of h "Suc h"] by auto
  next
    case greater
    with 3(3,4) have ht: "ht l = Suc h"  "ht r = h" by auto
    from ht 3(1,2,4) have "size1 (fib_tree (Suc h)) \<le> size1 l" by auto moreover
    from ht 3(1,2,4) have "size1 (fib_tree h) \<le> size1 r" by auto ultimately
    show ?thesis by auto
  next
    case less (* analogously *)
    with 3 have ht: "ht l = h"  "Suc h = ht r" by auto
    from ht 3 have "size1 (fib_tree h) \<le> size1 l" by auto moreover
    from ht 3 have "size1 (fib_tree (Suc h)) \<le> size1 r" by auto ultimately
    show ?thesis by auto
  qed
qed auto

theorem avl_size_bound: "avl t \<Longrightarrow> fib(height t + 2) \<le> size1 t" 
using fib_tree_minimal fib_tree_size1 by fastforce

end
