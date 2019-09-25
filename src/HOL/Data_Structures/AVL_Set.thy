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

type_synonym 'a avl_tree = "('a*nat) tree"

definition empty :: "'a avl_tree" where
"empty = Leaf"

text \<open>Invariant:\<close>

fun avl :: "'a avl_tree \<Rightarrow> bool" where
"avl Leaf = True" |
"avl (Node l (a,h) r) =
 ((height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

fun ht :: "'a avl_tree \<Rightarrow> nat" where
"ht Leaf = 0" |
"ht (Node l (a,h) r) = h"

definition node :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"node l a r = Node l (a, max (ht l) (ht r) + 1) r"

definition balL :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"balL l a r =
  (if ht l = ht r + 2 then
     case l of 
       Node bl (b, _) br \<Rightarrow>
         if ht bl < ht br then
           case br of
             Node cl (c, _) cr \<Rightarrow> node (node bl b cl) c (node cr a r)
         else node bl b (node br a r)
   else node l a r)"

definition balR :: "'a avl_tree \<Rightarrow> 'a \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"balR l a r =
   (if ht r = ht l + 2 then
      case r of
        Node bl (b, _) br \<Rightarrow>
          if ht bl > ht br then
            case bl of
              Node cl (c, _) cr \<Rightarrow> node (node l a cl) c (node cr b br)
          else node (node l a bl) b br
  else node l a r)"

fun insert :: "'a::linorder \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"insert x Leaf = Node Leaf (x, 1) Leaf" |
"insert x (Node l (a, h) r) = (case cmp x a of
   EQ \<Rightarrow> Node l (a, h) r |
   LT \<Rightarrow> balL (insert x l) a r |
   GT \<Rightarrow> balR l a (insert x r))"

fun split_max :: "'a avl_tree \<Rightarrow> 'a avl_tree * 'a" where
"split_max (Node l (a, _) r) =
  (if r = Leaf then (l,a) else let (r',a') = split_max r in (balL l a r', a'))"

lemmas split_max_induct = split_max.induct[case_names Node Leaf]

fun del_root :: "'a avl_tree \<Rightarrow> 'a avl_tree" where
"del_root (Node Leaf (a,h) r) = r" |
"del_root (Node l (a,h) Leaf) = l" |
"del_root (Node l (a,h) r) = (let (l', a') = split_max l in balR l' a' r)"

lemmas del_root_cases = del_root.cases[split_format(complete), case_names Leaf_t Node_Leaf Node_Node]

fun delete :: "'a::linorder \<Rightarrow> 'a avl_tree \<Rightarrow> 'a avl_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node l (a, h) r) =
  (case cmp x a of
     EQ \<Rightarrow> del_root (Node l (a, h) r) |
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

lemma inorder_split_maxD:
  "\<lbrakk> split_max t = (t',a); t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
   inorder t' @ [a] = inorder t"
by(induction t arbitrary: t' rule: split_max.induct)
  (auto simp: inorder_balL split: if_splits prod.splits tree.split)

lemma inorder_del_root:
  "inorder (del_root (Node l ah r)) = inorder l @ inorder r"
by(cases "Node l ah r" rule: del_root.cases)
  (auto simp: inorder_balL inorder_balR inorder_split_maxD split: if_splits prod.splits)

theorem inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR
    inorder_del_root inorder_split_maxD split: prod.splits)


subsection \<open>AVL invariants\<close>

text\<open>Essentially the AFP/AVL proofs\<close>


subsubsection \<open>Insertion maintains AVL balance\<close>

declare Let_def [simp]

lemma ht_height[simp]: "avl t \<Longrightarrow> ht t = height t"
by (cases t rule: tree2_cases) simp_all

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

lemma height_node[simp]: "height(node l a r) = max (height l) (height r) + 1"
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
proof(cases l rule: tree2_cases)
  case Leaf
  with assms show ?thesis by (simp add: node_def balL_def)
next
  case Node
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
proof(cases r rule: tree2_cases)
  case Leaf
  with assms show ?thesis by (simp add: node_def balR_def)
next
  case Node
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

theorem avl_insert:
  assumes "avl t"
  shows "avl(insert x t)"
        "(height (insert x t) = height t \<or> height (insert x t) = height t + 1)"
using assms
proof (induction t rule: tree2_induct)
  case (Node l a h r)
  case 1
  show ?case
  proof(cases "x = a")
    case True with Node 1 show ?thesis by simp
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True with Node 1 show ?thesis by (auto simp add:avl_balL)
    next
      case False with Node 1 \<open>x\<noteq>a\<close> show ?thesis by (auto simp add:avl_balR)
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
      proof(cases "height (insert x l) = height r + 2")
        case False with Node 2 \<open>x < a\<close> show ?thesis by (auto simp: height_balL2)
      next
        case True 
        hence "(height (balL (insert x l) a r) = height r + 2) \<or>
          (height (balL (insert x l) a r) = height r + 3)" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) simp_all
        thus ?thesis
        proof
          assume ?A with 2 \<open>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with True 1 Node(2) \<open>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    next
      case False
      show ?thesis 
      proof(cases "height (insert x r) = height l + 2")
        case False with Node 2 \<open>\<not>x < a\<close> show ?thesis by (auto simp: height_balR2)
      next
        case True 
        hence "(height (balR l a (insert x r)) = height l + 2) \<or>
          (height (balR l a (insert x r)) = height l + 3)"  (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) simp_all
        thus ?thesis 
        proof
          assume ?A with 2 \<open>\<not>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with True 1 Node(4) \<open>\<not>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    qed
  qed
qed simp_all


subsubsection \<open>Deletion maintains AVL balance\<close>

lemma avl_split_max:
  assumes "avl x" and "x \<noteq> Leaf"
  shows "avl (fst (split_max x))" "height x = height(fst (split_max x)) \<or>
         height x = height(fst (split_max x)) + 1"
using assms
proof (induct x rule: split_max_induct)
  case (Node l a h r)
  case 1
  thus ?case using Node
    by (auto simp: height_balL height_balL2 avl_balL split:prod.split)
next
  case (Node l a h r)
  case 2
  let ?r' = "fst (split_max r)"
  from \<open>avl x\<close> Node 2 have "avl l" and "avl r" by simp_all
  thus ?case using Node 2 height_balL[of l ?r' a] height_balL2[of l ?r' a]
    apply (auto split:prod.splits simp del:avl.simps) by arith+
qed auto

lemma avl_del_root:
  assumes "avl t" and "t \<noteq> Leaf"
  shows "avl(del_root t)" 
using assms
proof (cases t rule:del_root_cases)
  case (Node_Node ll ln lh lr n h rl rn rh rr)
  let ?l = "Node ll (ln, lh) lr"
  let ?r = "Node rl (rn, rh) rr"
  let ?l' = "fst (split_max ?l)"
  from \<open>avl t\<close> and Node_Node have "avl ?r" by simp
  from \<open>avl t\<close> and Node_Node have "avl ?l" by simp
  hence "avl(?l')" "height ?l = height(?l') \<or>
         height ?l = height(?l') + 1" by (rule avl_split_max,simp)+
  with \<open>avl t\<close> Node_Node have "height ?l' = height ?r \<or> height ?l' = height ?r + 1
            \<or> height ?r = height ?l' + 1 \<or> height ?r = height ?l' + 2" by fastforce
  with \<open>avl ?l'\<close> \<open>avl ?r\<close> have "avl(balR ?l' (snd(split_max ?l)) ?r)"
    by (rule avl_balR)
  with Node_Node show ?thesis by (auto split:prod.splits)
qed simp_all

lemma height_del_root:
  assumes "avl t" and "t \<noteq> Leaf" 
  shows "height t = height(del_root t) \<or> height t = height(del_root t) + 1"
using assms
proof (cases t rule: del_root_cases)
  case (Node_Node ll ln lh lr n h rl rn rh rr)
  let ?l = "Node ll (ln, lh) lr"
  let ?r = "Node rl (rn, rh) rr"
  let ?l' = "fst (split_max ?l)"
  let ?t' = "balR ?l' (snd(split_max ?l)) ?r"
  from \<open>avl t\<close> and Node_Node have "avl ?r" by simp
  from \<open>avl t\<close> and Node_Node have "avl ?l" by simp
  hence "avl(?l')"  by (rule avl_split_max,simp)
  have l'_height: "height ?l = height ?l' \<or> height ?l = height ?l' + 1" using \<open>avl ?l\<close> by (intro avl_split_max) auto
  have t_height: "height t = 1 + max (height ?l) (height ?r)" using \<open>avl t\<close> Node_Node by simp
  have "height t = height ?t' \<or> height t = height ?t' + 1" using  \<open>avl t\<close> Node_Node
  proof(cases "height ?r = height ?l' + 2")
    case False
    show ?thesis using l'_height t_height False
      by (subst height_balR2[OF \<open>avl ?l'\<close> \<open>avl ?r\<close> False])+ arith
  next
    case True
    show ?thesis
    proof(cases rule: disjE[OF height_balR[OF True \<open>avl ?l'\<close> \<open>avl ?r\<close>, of "snd (split_max ?l)"]])
      case 1 thus ?thesis using l'_height t_height True by arith
    next
      case 2 thus ?thesis using l'_height t_height True by arith
    qed
  qed
  thus ?thesis using Node_Node by (auto split:prod.splits)
qed simp_all

text\<open>Deletion maintains the AVL property:\<close>

theorem avl_delete:
  assumes "avl t" 
  shows "avl(delete x t)" and "height t = (height (delete x t)) \<or> height t = height (delete x t) + 1"
using assms
proof (induct t rule: tree2_induct)
  case (Node l n h r)
  case 1
  show ?case
  proof(cases "x = n")
    case True with Node 1 show ?thesis by (auto simp:avl_del_root)
  next
    case False
    show ?thesis 
    proof(cases "x<n")
      case True with Node 1 show ?thesis by (auto simp add:avl_balR)
    next
      case False with Node 1 \<open>x\<noteq>n\<close> show ?thesis by (auto simp add:avl_balL)
    qed
  qed
  case 2
  show ?case
  proof(cases "x = n")
    case True
    with 1 have "height (Node l (n,h) r) = height(del_root (Node l (n,h) r))
      \<or> height (Node l (n,h) r) = height(del_root (Node l (n,h) r)) + 1"
      by (subst height_del_root,simp_all)
    with True show ?thesis by simp
  next
    case False
    show ?thesis 
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
          assume ?A with \<open>x < n\<close> Node 2 show ?thesis by(auto simp: balR_def)
        next
          assume ?B with \<open>x < n\<close> Node 2 show ?thesis by(auto simp: balR_def)
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
          assume ?A with \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> Node 2 show ?thesis by(auto simp: balL_def)
        next
          assume ?B with \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> Node 2 show ?thesis by(auto simp: balL_def)
        qed
      qed
    qed
  qed
qed simp_all


subsection "Overall correctness"

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = avl
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
  case 6 thus ?case by (simp add: avl_insert(1))
next
  case 7 thus ?case by (simp add: avl_delete(1))
qed


subsection \<open>Height-Size Relation\<close>

text \<open>Based on theorems by Daniel St\"uwe, Manuel Eberl and Peter Lammich.\<close>

lemma height_invers: 
  "(height t = 0) = (t = Leaf)"
  "avl t \<Longrightarrow> (height t = Suc h) = (\<exists> l a r . t = Node l (a,Suc h) r)"
by (induction t) auto

text \<open>Any AVL tree of height \<open>h\<close> has at least \<open>fib (h+2)\<close> leaves:\<close>

lemma avl_fib_bound: "avl t \<Longrightarrow> height t = h \<Longrightarrow> fib (h+2) \<le> size1 t"
proof (induction h arbitrary: t rule: fib.induct)
  case 1 thus ?case by (simp add: height_invers)
next
  case 2 thus ?case by (cases t) (auto simp: height_invers)
next
  case (3 h)
  from "3.prems" obtain l a r where
    [simp]: "t = Node l (a,Suc(Suc h)) r" "avl l" "avl r"
    and C: "
      height r = Suc h \<and> height l = Suc h
    \<or> height r = Suc h \<and> height l = h
    \<or> height r = h \<and> height l = Suc h" (is "?C1 \<or> ?C2 \<or> ?C3")
    by (cases t) (simp, fastforce)
  {
    assume ?C1
    with "3.IH"(1)
    have "fib (h + 3) \<le> size1 l" "fib (h + 3) \<le> size1 r"
      by (simp_all add: eval_nat_numeral)
    hence ?case by (auto simp: eval_nat_numeral)
  } moreover {
    assume ?C2
    hence ?case using "3.IH"(1)[of r] "3.IH"(2)[of l] by auto
  } moreover {
    assume ?C3
    hence ?case using "3.IH"(1)[of l] "3.IH"(2)[of r] by auto
  } ultimately show ?case using C by blast
qed

lemma fib_alt_induct [consumes 1, case_names 1 2 rec]:
  assumes "n > 0" "P 1" "P 2" "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n) \<Longrightarrow> P (Suc (Suc n))"
  shows   "P n"
  using assms(1)
proof (induction n rule: fib.induct)
  case (3 n)
  thus ?case using assms by (cases n) (auto simp: eval_nat_numeral)
qed (insert assms, auto)

text \<open>An exponential lower bound for \<^const>\<open>fib\<close>:\<close>

lemma fib_lowerbound:
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  defines "c \<equiv> 1 / \<phi> ^ 2"
  assumes "n > 0"
  shows   "real (fib n) \<ge> c * \<phi> ^ n"
proof -
  have "\<phi> > 1" by (simp add: \<phi>_def)
  hence "c > 0" by (simp add: c_def)
  from \<open>n > 0\<close> show ?thesis
  proof (induction n rule: fib_alt_induct)
    case (rec n)
    have "c * \<phi> ^ Suc (Suc n) = \<phi> ^ 2 * (c * \<phi> ^ n)"
      by (simp add: field_simps power2_eq_square)
    also have "\<dots> \<le> (\<phi> + 1) * (c * \<phi> ^ n)"
      by (rule mult_right_mono) (insert \<open>c > 0\<close>, simp_all add: \<phi>_def power2_eq_square field_simps)
    also have "\<dots> = c * \<phi> ^ Suc n + c * \<phi> ^ n"
      by (simp add: field_simps)
    also have "\<dots> \<le> real (fib (Suc n)) + real (fib n)"
      by (intro add_mono rec.IH)
    finally show ?case by simp
  qed (insert \<open>\<phi> > 1\<close>, simp_all add: c_def power2_eq_square eval_nat_numeral)
qed

text \<open>The size of an AVL tree is (at least) exponential in its height:\<close>

lemma avl_size_lowerbound:
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  assumes "avl t"
  shows   "\<phi> ^ (height t) \<le> size1 t"
proof -
  have "\<phi> > 0" by(simp add: \<phi>_def add_pos_nonneg)
  hence "\<phi> ^ height t = (1 / \<phi> ^ 2) * \<phi> ^ (height t + 2)"
    by(simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> fib (height t + 2)"
    using fib_lowerbound[of "height t + 2"] by(simp add: \<phi>_def)
  also have "\<dots> \<le> size1 t"
    using avl_fib_bound[of t "height t"] assms by simp
  finally show ?thesis .
qed

text \<open>The height of an AVL tree is most \<^term>\<open>(1/log 2 \<phi>)\<close> \<open>\<approx> 1.44\<close> times worse
than \<^term>\<open>log 2 (size1 t)\<close>:\<close>

lemma  avl_height_upperbound:
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  assumes "avl t"
  shows   "height t \<le> (1/log 2 \<phi>) * log 2 (size1 t)"
proof -
  have "\<phi> > 0" "\<phi> > 1" by(auto simp: \<phi>_def pos_add_strict)
  hence "height t = log \<phi> (\<phi> ^ height t)" by(simp add: log_nat_power)
  also have "\<dots> \<le> log \<phi> (size1 t)"
    using avl_size_lowerbound[OF assms(2), folded \<phi>_def] \<open>1 < \<phi>\<close>
    by (simp add: le_log_of_power) 
  also have "\<dots> = (1/log 2 \<phi>) * log 2 (size1 t)"
    by(simp add: log_base_change[of 2 \<phi>])
  finally show ?thesis .
qed

end
