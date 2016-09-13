(* Author: Tobias Nipkow *)

section \<open>Creating Balanced Trees\<close>

theory Balance
imports
  "~~/src/HOL/Library/Tree"
  "~~/src/HOL/Library/Log_Nat"
begin

fun bal :: "'a list \<Rightarrow> nat \<Rightarrow> 'a tree * 'a list" where
"bal xs n = (if n=0 then (Leaf,xs) else
 (let m = n div 2;
      (l, ys) = bal xs m;
      (r, zs) = bal (tl ys) (n-1-m)
  in (Node l (hd ys) r, zs)))"

declare bal.simps[simp del]

definition balance_list :: "'a list \<Rightarrow> 'a tree" where
"balance_list xs = fst (bal xs (length xs))"

definition balance_tree :: "'a tree \<Rightarrow> 'a tree" where
"balance_tree = balance_list o inorder"

lemma bal_simps:
  "bal xs 0 = (Leaf, xs)"
  "n > 0 \<Longrightarrow>
   bal xs n =
  (let m = n div 2;
      (l, ys) = Balance.bal xs m;
      (r, zs) = Balance.bal (tl ys) (n-1-m)
  in (Node l (hd ys) r, zs))"
by(simp_all add: bal.simps)

text\<open>The following lemmas take advantage of the fact
that \<open>bal xs n\<close> yields a result even if \<open>n > length xs\<close>.\<close>
  
lemma size_bal: "bal xs n = (t,ys) \<Longrightarrow> size t = n"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n)
  thus ?case
    by(cases "n=0")
      (auto simp add: bal_simps Let_def split: prod.splits)
qed

lemma bal_inorder:
  "\<lbrakk> bal xs n = (t,ys); n \<le> length xs \<rbrakk>
  \<Longrightarrow> inorder t = take n xs \<and> ys = drop n xs"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis using 1 by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?n1 = "n div 2" let ?n2 = "n - 1 - ?n1"
    from "1.prems" obtain l r xs' where
      b1: "bal xs ?n1 = (l,xs')" and
      b2: "bal (tl xs') ?n2 = (r,ys)" and
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

corollary inorder_balance_list: "inorder(balance_list xs) = xs"
using bal_inorder[of xs "length xs"]
by (metis balance_list_def order_refl prod.collapse take_all)

lemma bal_height: "bal xs n = (t,ys) \<Longrightarrow> height t = floorlog 2 n"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: floorlog_def bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal xs (n div 2) = (l,xs')" and
      b2: "bal (tl xs') (n - 1 - n div 2) = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      by(auto simp: bal_simps Let_def split: prod.splits)
    let ?log1 = "floorlog 2 (n div 2)"
    let ?log2 = "floorlog 2 (n - 1 - n div 2)"
    have IH1: "height l = ?log1" using "1.IH"(1) b1 by simp
    have IH2: "height r = ?log2" using "1.IH"(2) b1 b2 by simp
    have "n div 2 \<ge> n - 1 - n div 2" by arith
    hence le: "?log2 \<le> ?log1" by(simp add:floorlog_mono)
    have "height t = max ?log1 ?log2 + 1" by (simp add: t IH1 IH2)
    also have "\<dots> = ?log1 + 1" using le by (simp add: max_absorb1)
    also have "\<dots> = floorlog 2 n" by (simp add: compute_floorlog)
    finally show ?thesis .
  qed
qed

lemma bal_min_height:
  "bal xs n = (t,ys) \<Longrightarrow> min_height t = floorlog 2 (n + 1) - 1"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: floorlog_def bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal xs (n div 2) = (l,xs')" and
      b2: "bal (tl xs') (n - 1 - n div 2) = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      by(auto simp: bal_simps Let_def split: prod.splits)
    let ?log1 = "floorlog 2 (n div 2 + 1) - 1"
    let ?log2 = "floorlog 2 (n - 1 - n div 2 + 1) - 1"
    let ?log2' = "floorlog 2 (n - n div 2) - 1"
    have "n - 1 - n div 2 + 1 = n - n div 2" by arith
    hence IH2: "min_height r = ?log2'" using "1.IH"(2) b1 b2 by simp
    have IH1: "min_height l = ?log1" using "1.IH"(1) b1 by simp
    have *: "floorlog 2 (n - n div 2) \<ge> 1" by (simp add: floorlog_def)
    have "n div 2 + 1 \<ge> n - n div 2" by arith
    with * have le: "?log2' \<le> ?log1" by(simp add: floorlog_mono diff_le_mono)
    have "min_height t = min ?log1 ?log2' + 1" by (simp add: t IH1 IH2)
    also have "\<dots> = ?log2' + 1" using le by (simp add: min_absorb2)
    also have "\<dots> = floorlog 2 (n - n div 2)" by(simp add: floorlog_def)
    also have "n - n div 2 = (n+1) div 2" by arith
    also have "floorlog 2 \<dots> = floorlog 2 (n+1) - 1"
      by (simp add: compute_floorlog)
    finally show ?thesis .
  qed
qed

lemma balanced_bal:
  assumes "bal xs n = (t,ys)" shows "balanced t"
proof -
  have "floorlog 2 n \<le> floorlog 2 (n+1)" by (rule floorlog_mono) auto
  thus ?thesis unfolding balanced_def
    using bal_height[OF assms] bal_min_height[OF assms] by linarith
qed

corollary size_balance_list[simp]: "size(balance_list xs) = length xs"
by (metis inorder_balance_list length_inorder)

corollary balanced_balance_list[simp]: "balanced (balance_list xs)"
by (metis balance_list_def balanced_bal prod.collapse)

lemma height_balance_list: "height(balance_list xs) = floorlog 2 (length xs)"
by (metis bal_height balance_list_def prod.collapse)

lemma inorder_balance_tree[simp]: "inorder(balance_tree t) = inorder t"
by(simp add: balance_tree_def inorder_balance_list)

lemma size_balance_tree[simp]: "size(balance_tree t) = size t"
by(simp add: balance_tree_def inorder_balance_list)

corollary balanced_balance_tree[simp]: "balanced (balance_tree t)"
by (simp add: balance_tree_def)

lemma height_balance_tree: "height(balance_tree t) = floorlog 2 (size t)"
by(simp add: balance_tree_def height_balance_list)

lemma wbalanced_bal: "bal xs n = (t,ys) \<Longrightarrow> wbalanced t"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n)
  show ?case
  proof cases
    assume "n = 0"
    thus ?thesis
      using "1.prems" by(simp add: bal_simps)
  next
    assume "n \<noteq> 0"
    with "1.prems" obtain l ys r zs where
      rec1: "bal xs (n div 2) = (l, ys)" and
      rec2: "bal (tl ys) (n - 1 - n div 2) = (r, zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp add: bal_simps Let_def split: prod.splits)
    have l: "wbalanced l" using "1.IH"(1)[OF \<open>n\<noteq>0\<close> refl rec1] .
    have "wbalanced r" using "1.IH"(2)[OF \<open>n\<noteq>0\<close> refl rec1[symmetric] refl rec2] .
    with l t size_bal[OF rec1] size_bal[OF rec2]
    show ?thesis by auto
  qed
qed

lemma wbalanced_balance_tree: "wbalanced (balance_tree t)"
by(simp add: balance_tree_def balance_list_def)
  (metis prod.collapse wbalanced_bal)

hide_const (open) bal

end
