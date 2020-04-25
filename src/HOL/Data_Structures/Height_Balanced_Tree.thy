(*
Author: Tobias Nipkow
*)

section "Height-Balanced Trees"

theory Height_Balanced_Tree
imports
  Cmp
  Isin2
begin

text \<open>Height-balanced trees (HBTs) can be seen as a generalization of AVL trees.
The code and the proofs were obtained by small modifications of the AVL theories.
This is an implementation of sets via HBTs.\<close>

type_synonym 'a hbt = "('a*nat) tree"

definition empty :: "'a hbt" where
"empty = Leaf"

text \<open>The maximal amount that the height of two siblings may differ.\<close>

consts m :: nat

text \<open>Invariant:\<close>

fun hbt :: "'a hbt \<Rightarrow> bool" where
"hbt Leaf = True" |
"hbt (Node l (a,n) r) =
 (abs(int(height l) - int(height r)) \<le> int(m+1) \<and>
  n = max (height l) (height r) + 1 \<and> hbt l \<and> hbt r)"

fun ht :: "'a hbt \<Rightarrow> nat" where
"ht Leaf = 0" |
"ht (Node l (a,n) r) = n"

definition node :: "'a hbt \<Rightarrow> 'a \<Rightarrow> 'a hbt \<Rightarrow> 'a hbt" where
"node l a r = Node l (a, max (ht l) (ht r) + 1) r"

definition balL :: "'a hbt \<Rightarrow> 'a \<Rightarrow> 'a hbt \<Rightarrow> 'a hbt" where
"balL AB b C =
  (if ht AB = ht C + m + 2 then
     case AB of 
       Node A (a, _) B \<Rightarrow>
         if ht A \<ge> ht B then node A a (node B b C)
         else
           case B of
             Node B\<^sub>1 (ab, _) B\<^sub>2 \<Rightarrow> node (node A a B\<^sub>1) ab (node B\<^sub>2 b C)
   else node AB b C)"

definition balR :: "'a hbt \<Rightarrow> 'a \<Rightarrow> 'a hbt \<Rightarrow> 'a hbt" where
"balR A a BC =
   (if ht BC = ht A + m + 2 then
      case BC of
        Node B (b, _) C \<Rightarrow>
          if ht B \<le> ht C then node (node A a B) b C
          else
            case B of
              Node B\<^sub>1 (ab, _) B\<^sub>2 \<Rightarrow> node (node A a B\<^sub>1) ab (node B\<^sub>2 b C)
  else node A a BC)"

fun insert :: "'a::linorder \<Rightarrow> 'a hbt \<Rightarrow> 'a hbt" where
"insert x Leaf = Node Leaf (x, 1) Leaf" |
"insert x (Node l (a, n) r) = (case cmp x a of
   EQ \<Rightarrow> Node l (a, n) r |
   LT \<Rightarrow> balL (insert x l) a r |
   GT \<Rightarrow> balR l a (insert x r))"

fun split_max :: "'a hbt \<Rightarrow> 'a hbt * 'a" where
"split_max (Node l (a, _) r) =
  (if r = Leaf then (l,a) else let (r',a') = split_max r in (balL l a r', a'))"

lemmas split_max_induct = split_max.induct[case_names Node Leaf]

fun delete :: "'a::linorder \<Rightarrow> 'a hbt \<Rightarrow> 'a hbt" where
"delete _ Leaf = Leaf" |
"delete x (Node l (a, n) r) =
  (case cmp x a of
     EQ \<Rightarrow> if l = Leaf then r
           else let (l', a') = split_max l in balR l' a' r |
     LT \<Rightarrow> balR (delete x l) a r |
     GT \<Rightarrow> balL l a (delete x r))"


subsection \<open>Functional Correctness Proofs\<close>


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

lemma inorder_split_maxD:
  "\<lbrakk> split_max t = (t',a); t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   inorder t' @ [a] = inorder t"
by(induction t arbitrary: t' rule: split_max.induct)
  (auto simp: inorder_balL split: if_splits prod.splits tree.split)

theorem inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR inorder_split_maxD split: prod.splits)


subsection \<open>Invariant preservation\<close>


subsubsection \<open>Insertion maintains balance\<close>

declare Let_def [simp]

lemma ht_height[simp]: "hbt t \<Longrightarrow> ht t = height t"
by (cases t rule: tree2_cases) simp_all

text \<open>First, a fast but relatively manual proof with many lemmas:\<close>

lemma height_balL:
  "\<lbrakk> hbt l; hbt r; height l = height r + m + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) = height r + m + 2 \<or>
   height (balL l a r) = height r + m + 3"
apply (cases l)
 apply (auto simp:node_def balL_def split:tree.split)
 by arith+

lemma height_balR:
  "\<lbrakk> hbt l; hbt r; height r = height l + m + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) = height l + m + 2 \<or>
   height (balR l a r) = height l + m + 3"
apply (cases r)
 apply(auto simp add:node_def balR_def split:tree.split)
 by arith+

lemma height_node[simp]: "height(node l a r) = max (height l) (height r) + 1"
by (simp add: node_def)

lemma height_balL2:
  "\<lbrakk> hbt l; hbt r; height l \<noteq> height r + m + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) = 1 + max (height l) (height r)"
by (cases l, cases r) (simp_all add: balL_def)

lemma height_balR2:
  "\<lbrakk> hbt l;  hbt r;  height r \<noteq> height l + m + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) = 1 + max (height l) (height r)"
by (cases l, cases r) (simp_all add: balR_def)

lemma hbt_balL: 
  "\<lbrakk> hbt l; hbt r; height r - m - 1 \<le> height l \<and> height l \<le> height r + m + 2 \<rbrakk> \<Longrightarrow> hbt(balL l a r)"
by(cases l, cases r)
  (auto simp: balL_def node_def split!: if_split tree.split)

lemma hbt_balR: 
  "\<lbrakk> hbt l; hbt r; height l - m - 1 \<le> height r \<and> height r \<le> height l + m + 2 \<rbrakk> \<Longrightarrow> hbt(balR l a r)"
by(cases r, cases l)
  (auto simp: balR_def node_def split!: if_split tree.split)

text\<open>Insertion maintains @{const hbt}. Requires simultaneous proof.\<close>

theorem hbt_insert:
  assumes "hbt t"
  shows "hbt(insert x t)"
        "(height (insert x t) = height t \<or> height (insert x t) = height t + 1)"
using assms
proof (induction t rule: tree2_induct)
  case (Node l a _ r)
  case 1
  show ?case
  proof(cases "x = a")
    case True with Node 1 show ?thesis by simp
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True with Node 1 show ?thesis by (auto intro!:hbt_balL)
    next
      case False with Node 1 \<open>x\<noteq>a\<close> show ?thesis by (auto intro!:hbt_balR)
    qed
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True with Node 1 show ?thesis by simp
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height (insert x l) = height r + m + 2")
        case False with Node 2 \<open>x < a\<close> show ?thesis by (auto simp: height_balL2)
      next
        case True 
        hence "(height (balL (insert x l) a r) = height r + m + 2) \<or>
          (height (balL (insert x l) a r) = height r + m + 3)" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) simp_all
        thus ?thesis
        proof
          assume ?A with Node(2) 2 True \<open>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with Node(2) 1 True \<open>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    next
      case False
      show ?thesis 
      proof(cases "height (insert x r) = height l + m + 2")
        case False with Node 2 \<open>\<not>x < a\<close> show ?thesis by (auto simp: height_balR2)
      next
        case True 
        hence "(height (balR l a (insert x r)) = height l + m + 2) \<or>
          (height (balR l a (insert x r)) = height l + m + 3)"  (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) simp_all
        thus ?thesis 
        proof
          assume ?A with Node(4) 2 True \<open>\<not>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with Node(4) 1 True \<open>\<not>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    qed
  qed
qed simp_all

text \<open>Now an automatic proof without lemmas:\<close>

theorem hbt_insert_auto: "hbt t \<Longrightarrow>
  hbt(insert x t) \<and> height (insert x t) \<in> {height t, height t + 1}"
apply (induction t rule: tree2_induct)
 (* if you want to save a few secs: apply (auto split!: if_split) *)
 apply (auto simp: balL_def balR_def node_def max_absorb1 max_absorb2 split!: if_split tree.split)
done


subsubsection \<open>Deletion maintains balance\<close>

lemma hbt_split_max:
  "\<lbrakk> hbt t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
  hbt (fst (split_max t)) \<and>
  height t \<in> {height(fst (split_max t)), height(fst (split_max t)) + 1}"
by(induct t rule: split_max_induct)
  (auto simp: balL_def node_def max_absorb2 split!: prod.split if_split tree.split)

text\<open>Deletion maintains @{const hbt}:\<close>

theorem hbt_delete:
  assumes "hbt t" 
  shows "hbt(delete x t)" and "height t = (height (delete x t)) \<or> height t = height (delete x t) + 1"
using assms
proof (induct t rule: tree2_induct)
  case (Node l a n r)
  case 1
  thus ?case
    using Node hbt_split_max[of l] by (auto intro!: hbt_balL hbt_balR split: prod.split)
  case 2
  show ?case
  proof(cases "x = a")
    case True then show ?thesis using 1 hbt_split_max[of l]
      by(auto simp: balR_def max_absorb2 split!: if_splits prod.split tree.split)
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + m + 2")
        case False with Node 1 \<open>x < a\<close> show ?thesis by(auto simp: balR_def)
      next
        case True 
        hence "(height (balR (delete x l) a r) = height (delete x l) + m + 2) \<or>
          height (balR (delete x l) a r) = height (delete x l) + m + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) auto
        thus ?thesis 
        proof
          assume ?A with \<open>x < a\<close> Node 2 show ?thesis by(auto simp: balR_def split!: if_splits)
        next
          assume ?B with \<open>x < a\<close> Node 2 show ?thesis by(auto simp: balR_def split!: if_splits)
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + m + 2")
        case False with Node 1 \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> show ?thesis by(auto simp: balL_def)
      next
        case True 
        hence "(height (balL l a (delete x r)) = height (delete x r) + m + 2) \<or>
          height (balL l a (delete x r)) = height (delete x r) + m + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) auto
        thus ?thesis 
        proof
          assume ?A with \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> Node 2 show ?thesis by(auto simp: balL_def split: if_splits)
        next
          assume ?B with \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> Node 2 show ?thesis by(auto simp: balL_def split: if_splits)
        qed
      qed
    qed
  qed
qed simp_all

text \<open>A more automatic proof.
Complete automation as for insertion seems hard due to resource requirements.\<close>

theorem hbt_delete_auto:
  assumes "hbt t" 
  shows "hbt(delete x t)" and "height t \<in> {height (delete x t), height (delete x t) + 1}"
using assms
proof (induct t rule: tree2_induct)
  case (Node l a n r)
  case 1
  show ?case
  proof(cases "x = a")
    case True thus ?thesis
      using 1 hbt_split_max[of l] by (auto intro!: hbt_balR split: prod.split)
  next
    case False thus ?thesis
      using Node 1 by (auto intro!: hbt_balL hbt_balR)
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True thus ?thesis
      using 1 hbt_split_max[of l]
      by(auto simp: balR_def max_absorb2 split!: if_splits prod.split tree.split)
  next
    case False thus ?thesis 
      using height_balL[of l "delete x r" a] height_balR[of "delete x l" r a] Node 1
        by(auto simp: balL_def balR_def split!: if_split)
  qed
qed simp_all


subsection "Overall correctness"

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = hbt
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: isin_set_inorder)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by (simp add: empty_def)
next
  case 6 thus ?case by (simp add: hbt_insert(1))
next
  case 7 thus ?case by (simp add: hbt_delete(1))
qed

end
