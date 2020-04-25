(*
Author: Tobias Nipkow
*)

subsection \<open>Invariant expressed via 3-way cases\<close>

theory AVL_Set
imports
  AVL_Set_Code
  "HOL-Number_Theory.Fib"
begin

fun avl :: "'a avl_tree \<Rightarrow> bool" where
"avl Leaf = True" |
"avl (Node l (a,n) r) =
 ((height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1) \<and> 
  n = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"


subsubsection \<open>Insertion maintains AVL balance\<close>

declare Let_def [simp]

lemma ht_height[simp]: "avl t \<Longrightarrow> ht t = height t"
by (cases t rule: tree2_cases) simp_all

text \<open>First, a fast but relatively manual proof with many lemmas:\<close>

lemma height_balL:
  "\<lbrakk> avl l; avl r; height l = height r + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) = height r + 2 \<or>
   height (balL l a r) = height r + 3"
by (cases l) (auto simp:node_def balL_def split:tree.split)
       
lemma height_balR:
  "\<lbrakk> avl l; avl r; height r = height l + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) = height l + 2 \<or>
   height (balR l a r) = height l + 3"
by (cases r) (auto simp add:node_def balR_def split:tree.split)

lemma height_node[simp]: "height(node l a r) = max (height l) (height r) + 1"
by (simp add: node_def)

lemma height_balL2:
  "\<lbrakk> avl l; avl r; height l \<noteq> height r + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) = 1 + max (height l) (height r)"
by (cases l, cases r) (simp_all add: balL_def)

lemma height_balR2:
  "\<lbrakk> avl l;  avl r;  height r \<noteq> height l + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) = 1 + max (height l) (height r)"
by (cases l, cases r) (simp_all add: balR_def)

lemma avl_balL: 
  "\<lbrakk> avl l; avl r; height r - 1 \<le> height l \<and> height l \<le> height r + 2 \<rbrakk> \<Longrightarrow> avl(balL l a r)"
by(cases l, cases r)
  (auto simp: balL_def node_def split!: if_split tree.split)

lemma avl_balR: 
  "\<lbrakk> avl l; avl r; height l - 1 \<le> height r \<and> height r \<le> height l + 2 \<rbrakk> \<Longrightarrow> avl(balR l a r)"
by(cases r, cases l)
  (auto simp: balR_def node_def split!: if_split tree.split)

text\<open>Insertion maintains the AVL property. Requires simultaneous proof.\<close>

theorem avl_insert:
  assumes "avl t"
  shows "avl(insert x t)"
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

text \<open>Now an automatic proof without lemmas:\<close>

theorem avl_insert_auto: "avl t \<Longrightarrow>
  avl(insert x t) \<and> height (insert x t) \<in> {height t, height t + 1}"
apply (induction t rule: tree2_induct)
 (* if you want to save a few secs: apply (auto split!: if_split) *)
 apply (auto simp: balL_def balR_def node_def max_absorb2 split!: if_split tree.split)
done


subsubsection \<open>Deletion maintains AVL balance\<close>

lemma avl_split_max:
  "\<lbrakk> avl t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
  avl (fst (split_max t)) \<and>
  height t \<in> {height(fst (split_max t)), height(fst (split_max t)) + 1}"
by(induct t rule: split_max_induct)
  (auto simp: balL_def node_def max_absorb2 split!: prod.split if_split tree.split)

text\<open>Deletion maintains the AVL property:\<close>

theorem avl_delete:
  assumes "avl t" 
  shows "avl(delete x t)" and "height t = (height (delete x t)) \<or> height t = height (delete x t) + 1"
using assms
proof (induct t rule: tree2_induct)
  case (Node l a n r)
  case 1
  thus ?case
    using Node avl_split_max[of l] by (auto simp: avl_balL avl_balR split: prod.split)
  case 2
  show ?case
  proof(cases "x = a")
    case True then show ?thesis using 1 avl_split_max[of l]
      by(auto simp: balR_def max_absorb2 split!: if_splits prod.split tree.split)
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + 2")
        case False with Node 1 \<open>x < a\<close> show ?thesis by(auto simp: balR_def)
      next
        case True 
        hence "(height (balR (delete x l) a r) = height (delete x l) + 2) \<or>
          height (balR (delete x l) a r) = height (delete x l) + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balR) auto
        thus ?thesis 
        proof
          assume ?A with \<open>x < a\<close> Node 2 show ?thesis by(auto simp: balR_def)
        next
          assume ?B with \<open>x < a\<close> Node 2 show ?thesis by(auto simp: balR_def)
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + 2")
        case False with Node 1 \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> show ?thesis by(auto simp: balL_def)
      next
        case True 
        hence "(height (balL l a (delete x r)) = height (delete x r) + 2) \<or>
          height (balL l a (delete x r)) = height (delete x r) + 3" (is "?A \<or> ?B")
          using Node 2 by (intro height_balL) auto
        thus ?thesis 
        proof
          assume ?A with \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> Node 2 show ?thesis by(auto simp: balL_def)
        next
          assume ?B with \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> Node 2 show ?thesis by(auto simp: balL_def)
        qed
      qed
    qed
  qed
qed simp_all

text \<open>A more automatic proof.
Complete automation as for insertion seems hard due to resource requirements.\<close>

theorem avl_delete_auto:
  assumes "avl t" 
  shows "avl(delete x t)" and "height t \<in> {height (delete x t), height (delete x t) + 1}"
using assms
proof (induct t rule: tree2_induct)
  case (Node l a n r)
  case 1
  show ?case
  proof(cases "x = a")
    case True thus ?thesis
      using 1 avl_split_max[of l] by (auto simp: avl_balR split: prod.split)
  next
    case False thus ?thesis
      using Node 1 by (auto simp: avl_balL avl_balR)
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True thus ?thesis
      using 1 avl_split_max[of l]
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

text \<open>Based on theorems by Daniel St\"uwe, Manuel Eberl and Peter Lammich, much simplified.\<close>

text \<open>Any AVL tree of height \<open>n\<close> has at least \<open>fib (n+2)\<close> leaves:\<close>

lemma avl_fib_bound: "avl t \<Longrightarrow> height t = n \<Longrightarrow> fib (n+2) \<le> size1 t"
proof (induction n arbitrary: t rule: fib.induct)
  case 1 thus ?case by (simp)
next
  case 2 thus ?case by (cases t) (auto)
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

text \<open>An exponential lower bound for \<^const>\<open>fib\<close>:\<close>

lemma fib_lowerbound:
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  shows "real (fib(n+2)) \<ge> \<phi> ^ n"
proof (induction n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp add: \<phi>_def real_le_lsqrt)
next
  case (3 n) term ?case
  have "\<phi> ^ Suc (Suc n) = \<phi> ^ 2 * \<phi> ^ n"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> = (\<phi> + 1) * \<phi> ^ n"
    by (simp_all add: \<phi>_def power2_eq_square field_simps)
  also have "\<dots> = \<phi> ^ Suc n + \<phi> ^ n"
      by (simp add: field_simps)
  also have "\<dots> \<le> real (fib (Suc n + 2)) + real (fib (n + 2))"
      by (intro add_mono "3.IH")
  finally show ?case by simp
qed

text \<open>The size of an AVL tree is (at least) exponential in its height:\<close>

lemma avl_size_lowerbound:
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  assumes "avl t"
  shows   "\<phi> ^ (height t) \<le> size1 t"
proof -
  have "\<phi> ^ height t \<le> fib (height t + 2)"
    unfolding \<phi>_def by(rule fib_lowerbound)
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
