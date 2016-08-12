(* Tobias Nipkow *)

section \<open>Creating a Balanced Tree from a List\<close>

theory Balance_List
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

definition "balance xs = fst (bal xs (length xs))"

lemma bal_inorder:
  "bal xs n = (t,ys) \<Longrightarrow> n \<le> length xs \<Longrightarrow> inorder t = take n xs \<and> ys = drop n xs"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis using 1 by (simp add: bal.simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?n1 = "n div 2" let ?n2 = "n - 1 - ?n1"
    from "1.prems" obtain l r xs' where
      b1: "bal xs ?n1 = (l,xs')" and
      b2: "bal (tl xs') ?n2 = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      using bal.simps[of xs n] by(auto simp: Let_def split: prod.splits)
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

corollary balance_inorder: "inorder(balance xs) = xs"
using bal_inorder[of xs "length xs"]
by (metis balance_def order_refl prod.collapse take_all)

lemma bal_height: "bal xs n = (t,ys) \<Longrightarrow> height t = floorlog 2 n"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: floorlog_def bal.simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal xs (n div 2) = (l,xs')" and
      b2: "bal (tl xs') (n - 1 - n div 2) = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      using bal.simps[of xs n] by(auto simp: Let_def split: prod.splits)
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
      using "1.prems" by (simp add: floorlog_def bal.simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal xs (n div 2) = (l,xs')" and
      b2: "bal (tl xs') (n - 1 - n div 2) = (r,ys)" and
      t: "t = \<langle>l, hd xs', r\<rangle>"
      using bal.simps[of xs n] by(auto simp: Let_def split: prod.splits)
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
  assumes "bal xs n = (t,ys)" shows "height t - min_height t \<le> 1"
proof -
  have "floorlog 2 n \<le> floorlog 2 (n+1)" by (rule floorlog_mono) auto
  thus ?thesis
    using bal_height[OF assms] bal_min_height[OF assms] by arith
qed

corollary balanced_balance: "height(balance xs) - min_height(balance xs) \<le> 1"
by (metis balance_def balanced_bal prod.collapse)

end
