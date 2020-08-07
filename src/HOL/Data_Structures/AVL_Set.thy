(* Author: Tobias Nipkow *)

subsection \<open>Invariant\<close>

theory AVL_Set
imports
  AVL_Set_Code
  "HOL-Number_Theory.Fib"
begin

fun avl :: "'a tree_ht \<Rightarrow> bool" where
"avl Leaf = True" |
"avl (Node l (a,n) r) =
 (abs(int(height l) - int(height r)) \<le> 1 \<and>
  n = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

subsubsection \<open>Insertion maintains AVL balance\<close>

declare Let_def [simp]

lemma ht_height[simp]: "avl t \<Longrightarrow> ht t = height t"
by (cases t rule: tree2_cases) simp_all

text \<open>First, a fast but relatively manual proof with many lemmas:\<close>

lemma height_balL:
  "\<lbrakk> avl l; avl r; height l = height r + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) \<in> {height r + 2, height r + 3}"
by (auto simp:node_def balL_def split:tree.split)

lemma height_balR:
  "\<lbrakk> avl l; avl r; height r = height l + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) : {height l + 2, height l + 3}"
by(auto simp add:node_def balR_def split:tree.split)

lemma height_node[simp]: "height(node l a r) = max (height l) (height r) + 1"
by (simp add: node_def)

lemma height_balL2:
  "\<lbrakk> avl l; avl r; height l \<noteq> height r + 2 \<rbrakk> \<Longrightarrow>
   height (balL l a r) = 1 + max (height l) (height r)"
by (simp_all add: balL_def)

lemma height_balR2:
  "\<lbrakk> avl l;  avl r;  height r \<noteq> height l + 2 \<rbrakk> \<Longrightarrow>
   height (balR l a r) = 1 + max (height l) (height r)"
by (simp_all add: balR_def)

lemma avl_balL: 
  "\<lbrakk> avl l; avl r; height r - 1 \<le> height l \<and> height l \<le> height r + 2 \<rbrakk> \<Longrightarrow> avl(balL l a r)"
by(auto simp: balL_def node_def split!: if_split tree.split)

lemma avl_balR: 
  "\<lbrakk> avl l; avl r; height l - 1 \<le> height r \<and> height r \<le> height l + 2 \<rbrakk> \<Longrightarrow> avl(balR l a r)"
by(auto simp: balR_def node_def split!: if_split tree.split)

text\<open>Insertion maintains the AVL property. Requires simultaneous proof.\<close>

theorem avl_insert:
  "avl t \<Longrightarrow> avl(insert x t)"
  "avl t \<Longrightarrow> height (insert x t) \<in> {height t, height t + 1}"
proof (induction t rule: tree2_induct)
  case (Node l a _ r)
  case 1
  show ?case
  proof(cases "x = a")
    case True with 1 show ?thesis by simp
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True with 1 Node(1,2) show ?thesis by (auto intro!:avl_balL)
    next
      case False with 1 Node(3,4) \<open>x\<noteq>a\<close> show ?thesis by (auto intro!:avl_balR)
    qed
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True with 2 show ?thesis by simp
  next
    case False
    show ?thesis 
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height (insert x l) = height r + 2")
        case False with 2 Node(1,2) \<open>x < a\<close> show ?thesis by (auto simp: height_balL2)
      next
        case True 
        hence "(height (balL (insert x l) a r) = height r + 2) \<or>
          (height (balL (insert x l) a r) = height r + 3)" (is "?A \<or> ?B")
          using 2 Node(1,2) height_balL[OF _ _ True] by simp
        thus ?thesis
        proof
          assume ?A with 2 \<open>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with 2 Node(2) True \<open>x < a\<close> show ?thesis by (simp) arith
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height (insert x r) = height l + 2")
        case False with 2 Node(3,4) \<open>\<not>x < a\<close> show ?thesis by (auto simp: height_balR2)
      next
        case True 
        hence "(height (balR l a (insert x r)) = height l + 2) \<or>
          (height (balR l a (insert x r)) = height l + 3)"  (is "?A \<or> ?B")
          using 2 Node(3) height_balR[OF _ _ True] by simp
        thus ?thesis
        proof
          assume ?A with 2 \<open>\<not>x < a\<close> show ?thesis by (auto)
        next
          assume ?B with 2 Node(4) True \<open>\<not>x < a\<close> show ?thesis by (simp) arith
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
  "avl t \<Longrightarrow> avl(delete x t)"
  "avl t \<Longrightarrow> height t \<in> {height (delete x t), height (delete x t) + 1}"
proof (induct t rule: tree2_induct)
  case (Node l a n r)
  case 1
  show ?case
  proof(cases "x = a")
    case True thus ?thesis
      using 1 avl_split_max[of l] by (auto intro!: avl_balR split: prod.split)
  next
    case False thus ?thesis
      using Node 1 by (auto intro!: avl_balL avl_balR)
  qed
  case 2
  show ?case
  proof(cases "x = a")
    case True thus ?thesis using 2 avl_split_max[of l]
      by(auto simp: balR_def max_absorb2 split!: if_splits prod.split tree.split)
  next
    case False
    show ?thesis
    proof(cases "x<a")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + 2")
        case False
        thus ?thesis using 2 Node(1,2) \<open>x < a\<close> by(auto simp: balR_def)
      next
        case True
        thus ?thesis using height_balR[OF _ _ True, of a] 2 Node(1,2) \<open>x < a\<close> by simp linarith
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + 2")
        case False
        thus ?thesis using 2 Node(3,4) \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> by(auto simp: balL_def)
      next
        case True
        thus ?thesis
          using height_balL[OF _ _ True, of a] 2 Node(3,4) \<open>\<not>x < a\<close> \<open>x \<noteq> a\<close> by simp linarith
      qed
    qed
  qed
qed simp_all

text \<open>A more automatic proof.
Complete automation as for insertion seems hard due to resource requirements.\<close>

theorem avl_delete_auto:
  "avl t \<Longrightarrow> avl(delete x t)"
  "avl t \<Longrightarrow> height t \<in> {height (delete x t), height (delete x t) + 1}"
proof (induct t rule: tree2_induct)
  case (Node l a n r)
  case 1
  thus ?case
    using Node avl_split_max[of l] by (auto intro!: avl_balL avl_balR split: prod.split)
  case 2
  show ?case
    using 2 Node avl_split_max[of l]
      by auto
         (auto simp: balL_def balR_def max_absorb1 max_absorb2  split!: tree.splits prod.splits if_splits)
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

text \<open>Any AVL tree of height \<open>n\<close> has at least \<open>fib (n+2)\<close> leaves:\<close>

theorem avl_fib_bound:
  "avl t \<Longrightarrow> fib(height t + 2) \<le> size1 t"
proof (induction rule: tree2_induct)
  case (Node l a h r)
  have 1: "height l + 1 \<le> height r + 2" and 2: "height r + 1 \<le> height l + 2"
    using Node.prems by auto
  have "fib (max (height l) (height r) + 3) \<le> size1 l + size1 r"
  proof cases
    assume "height l \<ge> height r"
    hence "fib (max (height l) (height r) + 3) = fib (height l + 3)"
      by(simp add: max_absorb1)
    also have "\<dots> = fib (height l + 2) + fib (height l + 1)"
      by (simp add: numeral_eq_Suc)
    also have "\<dots> \<le> size1 l + fib (height l + 1)"
      using Node by (simp)
    also have "\<dots> \<le> size1 r + size1 l"
      using Node fib_mono[OF 1] by auto
    also have "\<dots> = size1 (Node l (a,h) r)"
      by simp
    finally show ?thesis 
      by (simp)
  next
    assume "\<not> height l \<ge> height r"
    hence "fib (max (height l) (height r) + 3) = fib (height r + 3)"
      by(simp add: max_absorb1)
    also have "\<dots> = fib (height r + 2) + fib (height r + 1)"
      by (simp add: numeral_eq_Suc)
    also have "\<dots> \<le> size1 r + fib (height r + 1)"
      using Node by (simp)
    also have "\<dots> \<le> size1 r + size1 l"
      using Node fib_mono[OF 2] by auto
    also have "\<dots> = size1 (Node l (a,h) r)"
      by simp
    finally show ?thesis 
      by (simp)
  qed
  also have "\<dots> = size1 (Node l (a,h) r)"
    by simp
  finally show ?case by (simp del: fib.simps add: numeral_eq_Suc)
qed auto

lemma avl_fib_bound_auto: "avl t \<Longrightarrow> fib (height t + 2) \<le> size1 t"
proof (induction t rule: tree2_induct)
  case Leaf thus ?case by (simp)
next
  case (Node l a h r)
  have 1: "height l + 1 \<le> height r + 2" and 2: "height r + 1 \<le> height l + 2"
    using Node.prems by auto
  have left: "height l \<ge> height r \<Longrightarrow> ?case" (is "?asm \<Longrightarrow> _")
    using Node fib_mono[OF 1] by (simp add: max.absorb1)
  have right: "height l \<le> height r \<Longrightarrow> ?case"
    using Node fib_mono[OF 2] by (simp add: max.absorb2)
  show ?case using left right using Node.prems by simp linarith
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
  case (3 n)
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
    using avl_fib_bound[of t] assms by simp
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
