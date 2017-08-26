(* Author: Tobias Nipkow *)

section \<open>Creating Balanced Trees\<close>

theory Balance
imports
  "HOL-Library.Tree_Real"
begin

fun bal :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a tree * 'a list" where
"bal n xs = (if n=0 then (Leaf,xs) else
 (let m = n div 2;
      (l, ys) = bal m xs;
      (r, zs) = bal (n-1-m) (tl ys)
  in (Node l (hd ys) r, zs)))"

declare bal.simps[simp del]

definition bal_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a tree" where
"bal_list n xs = fst (bal n xs)"

definition balance_list :: "'a list \<Rightarrow> 'a tree" where
"balance_list xs = bal_list (length xs) xs"

definition bal_tree :: "nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"bal_tree n t = bal_list n (inorder t)"

definition balance_tree :: "'a tree \<Rightarrow> 'a tree" where
"balance_tree t = bal_tree (size t) t"

lemma bal_simps:
  "bal 0 xs = (Leaf, xs)"
  "n > 0 \<Longrightarrow>
   bal n xs =
  (let m = n div 2;
      (l, ys) = bal m xs;
      (r, zs) = bal (n-1-m) (tl ys)
  in (Node l (hd ys) r, zs))"
by(simp_all add: bal.simps)

text\<open>Some of the following lemmas take advantage of the fact
that \<open>bal xs n\<close> yields a result even if \<open>n > length xs\<close>.\<close>
  
lemma size_bal: "bal n xs = (t,ys) \<Longrightarrow> size t = n"
proof(induction n xs arbitrary: t ys rule: bal.induct)
  case (1 n xs)
  thus ?case
    by(cases "n=0")
      (auto simp add: bal_simps Let_def split: prod.splits)
qed

lemma bal_inorder:
  "\<lbrakk> bal n xs = (t,ys); n \<le> length xs \<rbrakk>
  \<Longrightarrow> inorder t = take n xs \<and> ys = drop n xs"
proof(induction n xs arbitrary: t ys rule: bal.induct)
  case (1 n xs) show ?case
  proof cases
    assume "n = 0" thus ?thesis using 1 by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?n1 = "n div 2" let ?n2 = "n - 1 - ?n1"
    from "1.prems" obtain l r xs' where
      b1: "bal ?n1 xs = (l,xs')" and
      b2: "bal ?n2 (tl xs') = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      by(auto simp: Let_def bal_simps split: prod.splits)
    have IH1: "inorder l = take ?n1 xs \<and> xs' = drop ?n1 xs"
      using b1 "1.prems" by(intro "1.IH"(1)) auto
    have IH2: "inorder r = take ?n2 (tl xs') \<and> ys = drop ?n2 (tl xs')"
      using b1 b2 IH1 "1.prems" by(intro "1.IH"(2)) auto
    have "drop (n div 2) xs \<noteq> []" using "1.prems"(2) by simp
    hence "hd (drop ?n1 xs) # take ?n2 (tl (drop ?n1 xs)) = take (?n2 + 1) (drop ?n1 xs)"
      by (metis Suc_eq_plus1 take_Suc)
    hence *: "inorder t = take n xs" using t IH1 IH2
      using take_add[of ?n1 "?n2+1" xs] by(simp)
    have "n - n div 2 + n div 2 = n" by simp
    hence "ys = drop n xs" using IH1 IH2 by (simp add: drop_Suc[symmetric])
    thus ?thesis using * by blast
  qed
qed

corollary inorder_bal_list[simp]:
  "n \<le> length xs \<Longrightarrow> inorder(bal_list n xs) = take n xs"
unfolding bal_list_def by (metis bal_inorder eq_fst_iff)

corollary inorder_balance_list[simp]: "inorder(balance_list xs) = xs"
by(simp add: balance_list_def)

corollary inorder_bal_tree:
  "n \<le> size t \<Longrightarrow> inorder(bal_tree n t) = take n (inorder t)"
by(simp add: bal_tree_def)

corollary inorder_balance_tree[simp]: "inorder(balance_tree t) = inorder t"
by(simp add: balance_tree_def inorder_bal_tree)

corollary size_bal_list[simp]: "size(bal_list n xs) = n"
unfolding bal_list_def by (metis prod.collapse size_bal)

corollary size_balance_list[simp]: "size(balance_list xs) = length xs"
by (simp add: balance_list_def)

corollary size_bal_tree[simp]: "size(bal_tree n t) = n"
by(simp add: bal_tree_def)

corollary size_balance_tree[simp]: "size(balance_tree t) = size t"
by(simp add: balance_tree_def)

lemma min_height_bal:
  "bal n xs = (t,ys) \<Longrightarrow> min_height t = nat(\<lfloor>log 2 (n + 1)\<rfloor>)"
proof(induction n xs arbitrary: t ys rule: bal.induct)
  case (1 n xs) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal (n div 2) xs = (l,xs')" and
      b2: "bal (n - 1 - n div 2) (tl xs') = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      by(auto simp: bal_simps Let_def split: prod.splits)
    let ?log1 = "nat (floor(log 2 (n div 2 + 1)))"
    let ?log2 = "nat (floor(log 2 (n - 1 - n div 2 + 1)))"
    have IH1: "min_height l = ?log1" using "1.IH"(1) b1 by simp
    have IH2: "min_height r = ?log2" using "1.IH"(2) b1 b2 by simp
    have "(n+1) div 2 \<ge> 1" by arith
    hence 0: "log 2 ((n+1) div 2) \<ge> 0" by simp
    have "n - 1 - n div 2 + 1 \<le> n div 2 + 1" by arith
    hence le: "?log2 \<le> ?log1"
      by(simp add: nat_mono floor_mono)
    have "min_height t = min ?log1 ?log2 + 1" by (simp add: t IH1 IH2)
    also have "\<dots> = ?log2 + 1" using le by (simp add: min_absorb2)
    also have "n - 1 - n div 2 + 1 = (n+1) div 2" by linarith
    also have "nat (floor(log 2 ((n+1) div 2))) + 1
       = nat (floor(log 2 ((n+1) div 2) + 1))"
      using 0 by linarith
    also have "\<dots> = nat (floor(log 2 (n + 1)))"
      using floor_log2_div2[of "n+1"] by (simp add: log_mult)
    finally show ?thesis .
  qed
qed

lemma height_bal:
  "bal n xs = (t,ys) \<Longrightarrow> height t = nat \<lceil>log 2 (n + 1)\<rceil>"
proof(induction n xs arbitrary: t ys rule: bal.induct)
  case (1 n xs) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal (n div 2) xs = (l,xs')" and
      b2: "bal (n - 1 - n div 2) (tl xs') = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      by(auto simp: bal_simps Let_def split: prod.splits)
    let ?log1 = "nat \<lceil>log 2 (n div 2 + 1)\<rceil>"
    let ?log2 = "nat \<lceil>log 2 (n - 1 - n div 2 + 1)\<rceil>"
    have IH1: "height l = ?log1" using "1.IH"(1) b1 by simp
    have IH2: "height r = ?log2" using "1.IH"(2) b1 b2 by simp
    have 0: "log 2 (n div 2 + 1) \<ge> 0" by auto
    have "n - 1 - n div 2 + 1 \<le> n div 2 + 1" by arith
    hence le: "?log2 \<le> ?log1"
      by(simp add: nat_mono ceiling_mono del: nat_ceiling_le_eq)
    have "height t = max ?log1 ?log2 + 1" by (simp add: t IH1 IH2)
    also have "\<dots> = ?log1 + 1" using le by (simp add: max_absorb1)
    also have "\<dots> = nat \<lceil>log 2 (n div 2 + 1) + 1\<rceil>" using 0 by linarith
    also have "\<dots> = nat \<lceil>log 2 (n + 1)\<rceil>"
      using ceiling_log2_div2[of "n+1"] by (simp)
    finally show ?thesis .
  qed
qed

lemma balanced_bal:
  assumes "bal n xs = (t,ys)" shows "balanced t"
unfolding balanced_def
using height_bal[OF assms] min_height_bal[OF assms]
by linarith

lemma height_bal_list:
  "n \<le> length xs \<Longrightarrow> height (bal_list n xs) = nat \<lceil>log 2 (n + 1)\<rceil>"
unfolding bal_list_def by (metis height_bal prod.collapse)

lemma height_balance_list:
  "height (balance_list xs) = nat \<lceil>log 2 (length xs + 1)\<rceil>"
by (simp add: balance_list_def height_bal_list)

corollary height_bal_tree:
  "n \<le> length xs \<Longrightarrow> height (bal_tree n t) = nat\<lceil>log 2 (n + 1)\<rceil>"
unfolding bal_list_def bal_tree_def
using height_bal prod.exhaust_sel by blast

corollary height_balance_tree:
  "height (balance_tree t) = nat\<lceil>log 2 (size t + 1)\<rceil>"
by (simp add: bal_tree_def balance_tree_def height_bal_list)

corollary balanced_bal_list[simp]: "balanced (bal_list n xs)"
unfolding bal_list_def by (metis  balanced_bal prod.collapse)

corollary balanced_balance_list[simp]: "balanced (balance_list xs)"
by (simp add: balance_list_def)

corollary balanced_bal_tree[simp]: "balanced (bal_tree n t)"
by (simp add: bal_tree_def)

corollary balanced_balance_tree[simp]: "balanced (balance_tree t)"
by (simp add: balance_tree_def)

lemma wbalanced_bal: "bal n xs = (t,ys) \<Longrightarrow> wbalanced t"
proof(induction n xs arbitrary: t ys rule: bal.induct)
  case (1 n xs)
  show ?case
  proof cases
    assume "n = 0"
    thus ?thesis
      using "1.prems" by(simp add: bal_simps)
  next
    assume "n \<noteq> 0"
    with "1.prems" obtain l ys r zs where
      rec1: "bal (n div 2) xs = (l, ys)" and
      rec2: "bal (n - 1 - n div 2) (tl ys) = (r, zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp add: bal_simps Let_def split: prod.splits)
    have l: "wbalanced l" using "1.IH"(1)[OF \<open>n\<noteq>0\<close> refl rec1] .
    have "wbalanced r" using "1.IH"(2)[OF \<open>n\<noteq>0\<close> refl rec1[symmetric] refl rec2] .
    with l t size_bal[OF rec1] size_bal[OF rec2]
    show ?thesis by auto
  qed
qed

text\<open>An alternative proof via @{thm balanced_if_wbalanced}:\<close>
lemma "bal n xs = (t,ys) \<Longrightarrow> balanced t"
by(rule balanced_if_wbalanced[OF wbalanced_bal])

lemma wbalanced_bal_list[simp]: "wbalanced (bal_list n xs)"
by(simp add: bal_list_def) (metis prod.collapse wbalanced_bal)

lemma wbalanced_balance_list[simp]: "wbalanced (balance_list xs)"
by(simp add: balance_list_def)

lemma wbalanced_bal_tree[simp]: "wbalanced (bal_tree n t)"
by(simp add: bal_tree_def)

lemma wbalanced_balance_tree: "wbalanced (balance_tree t)"
by (simp add: balance_tree_def)

hide_const (open) bal

end
