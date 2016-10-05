(* Author: Tobias Nipkow *)

section \<open>Creating Balanced Trees\<close>

theory Balance
imports
  Complex_Main
  "~~/src/HOL/Library/Tree"
begin

(* mv *)

text \<open>The lemmas about \<open>floor\<close> and \<open>ceiling\<close> of \<open>log 2\<close> should be generalized
from 2 to \<open>n\<close> and should be made executable. \<close>

lemma floor_log_nat: fixes b n k :: nat
assumes "b \<ge> 2" "b^n \<le> k" "k < b^(n+1)"
shows "floor (log b (real k)) = int(n)"
proof -
  have "k \<ge> 1"
    using assms(1,2) one_le_power[of b n] by linarith
  show ?thesis
  proof(rule floor_eq2)
    show "int n \<le> log b k"
      using assms(1,2) \<open>k \<ge> 1\<close>
      by(simp add: powr_realpow le_log_iff of_nat_power[symmetric] del: of_nat_power)
  next
    have "real k < b powr (real(n + 1))" using assms(1,3)
      by (simp only: powr_realpow) (metis of_nat_less_iff of_nat_power)
    thus "log b k < real_of_int (int n) + 1"
      using assms(1) \<open>k \<ge> 1\<close> by(simp add: log_less_iff add_ac)
  qed
qed

lemma ceil_log_nat: fixes b n k :: nat
assumes "b \<ge> 2" "b^n < k" "k \<le> b^(n+1)"
shows "ceiling (log b (real k)) = int(n)+1"
proof(rule ceiling_eq)
  show "int n < log b k"
    using assms(1,2)
    by(simp add: powr_realpow less_log_iff of_nat_power[symmetric] del: of_nat_power)
next
  have "real k \<le> b powr (real(n + 1))"
    using assms(1,3)
    by (simp only: powr_realpow) (metis of_nat_le_iff of_nat_power)
  thus "log b k \<le> real_of_int (int n) + 1"
    using assms(1,2) by(simp add: log_le_iff add_ac)
qed

lemma ex_power_ivl1: fixes b k :: nat assumes "b \<ge> 2"
shows "k \<ge> 1 \<Longrightarrow> \<exists>n. b^n \<le> k \<and> k < b^(n+1)" (is "_ \<Longrightarrow> \<exists>n. ?P k n")
proof(induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  show ?case
  proof cases
    assume "k=0"
    hence "?P (Suc k) 0"
      using assms by simp
    thus ?case ..
  next
    assume "k\<noteq>0"
    with Suc obtain n where IH: "?P k n" by auto
    show ?case
    proof (cases "k = b^(n+1) - 1")
      case True
      hence "?P (Suc k) (n+1)" using assms
        by (simp add: not_less_eq_eq[symmetric])
      thus ?thesis ..
    next
      case False
      hence "?P (Suc k) n" using IH by auto
      thus ?thesis ..
    qed
  qed
qed

lemma ex_power_ivl2: fixes b k :: nat assumes "b \<ge> 2" "(k::nat) \<ge> 2"
shows "\<exists>n. b^n < k \<and> k \<le> b^(n+1)"
proof -
  have "1 \<le> k - 1"
    using assms(2) by arith
  from ex_power_ivl1[OF assms(1) this]
  obtain n where "b ^ n \<le> k - 1 \<and> k - 1 < b ^ (n + 1)" ..
  hence "b^n < k \<and> k \<le> b^(n+1)"
    using assms by auto
  thus ?thesis ..
qed

lemma ceil_log2_div2: assumes "n \<ge> 2"
shows "ceiling(log 2 (real n)) = ceiling(log 2 ((n-1) div 2 + 1)) + 1"
proof cases
  assume "n=2"
  thus ?thesis by simp
next
  let ?m = "(n-1) div 2 + 1"
  assume "n\<noteq>2"
  hence "2 \<le> ?m"
    using assms by arith
  then obtain i where i: "2 ^ i < ?m" "?m \<le> 2 ^ (i + 1)"
    using ex_power_ivl2[of 2 ?m] by auto
  have "n \<le> 2*?m"
    by arith
  also have "2*?m \<le> 2 ^ ((i+1)+1)"
    using i(2) by simp
  finally have *: "n \<le> \<dots>" .
  have "2^(i+1) < n"
    using i(1) by (auto simp add: less_Suc_eq_0_disj)
  from ceil_log_nat[OF _ this *] ceil_log_nat[OF _ i]
  show ?thesis by simp
qed

lemma floor_log2_div2: fixes n :: nat assumes "n \<ge> 2"
shows "floor(log 2 n) = floor(log 2 (n div 2)) + 1"
proof cases
  assume "n=2"
  thus ?thesis by simp
next
  let ?m = "n div 2"
  assume "n\<noteq>2"
  hence "1 \<le> ?m"
    using assms by arith
  then obtain i where i: "2 ^ i \<le> ?m" "?m < 2 ^ (i + 1)"
    using ex_power_ivl1[of 2 ?m] by auto
  have "2^(i+1) \<le> 2*?m"
    using i(1) by simp
  also have "2*?m \<le> n"
    by arith
  finally have *: "2^(i+1) \<le> \<dots>" .
  have "n < 2^(i+1+1)"
    using i(2) by simp
  from floor_log_nat[OF _ * this] floor_log_nat[OF _ i]
  show ?thesis by simp
qed

(* end of mv *)

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
      (l, ys) = bal xs m;
      (r, zs) = bal (tl ys) (n-1-m)
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

corollary inorder_balance_tree[simp]: "inorder(balance_tree t) = inorder t"
by(simp add: balance_tree_def inorder_balance_list)

corollary size_balance_list[simp]: "size(balance_list xs) = length xs"
by (metis inorder_balance_list length_inorder)

corollary size_balance_tree[simp]: "size(balance_tree t) = size t"
by(simp add: balance_tree_def inorder_balance_list)

lemma min_height_bal:
  "bal xs n = (t,ys) \<Longrightarrow> min_height t = nat(floor(log 2 (n + 1)))"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal xs (n div 2) = (l,xs')" and
      b2: "bal (tl xs') (n - 1 - n div 2) = (r,ys)" and
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
  "bal xs n = (t,ys) \<Longrightarrow> height t = nat \<lceil>log 2 (n + 1)\<rceil>"
proof(induction xs n arbitrary: t ys rule: bal.induct)
  case (1 xs n) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r xs' where
      b1: "bal xs (n div 2) = (l,xs')" and
      b2: "bal (tl xs') (n - 1 - n div 2) = (r,ys)" and
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
      using ceil_log2_div2[of "n+1"] by (simp)
    finally show ?thesis .
  qed
qed

lemma balanced_bal:
  assumes "bal xs n = (t,ys)" shows "balanced t"
unfolding balanced_def
using height_bal[OF assms] min_height_bal[OF assms]
by linarith

lemma height_balance_list:
  "height (balance_list xs) = nat \<lceil>log 2 (length xs + 1)\<rceil>"
by (metis balance_list_def height_bal prod.collapse)

corollary height_balance_tree:
  "height (balance_tree t) = nat(ceiling(log 2 (size t + 1)))"
by(simp add: balance_tree_def height_balance_list)

corollary balanced_balance_list[simp]: "balanced (balance_list xs)"
by (metis balance_list_def balanced_bal prod.collapse)

corollary balanced_balance_tree[simp]: "balanced (balance_tree t)"
by (simp add: balance_tree_def)

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
