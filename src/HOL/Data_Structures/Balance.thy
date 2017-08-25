(* Author: Tobias Nipkow *)

section \<open>Creating Balanced Trees\<close>

theory Balance
imports
  "HOL-Library.Tree_Real"
begin

(* mv *)

text \<open>The lemmas about \<open>floor\<close> and \<open>ceiling\<close> of \<open>log 2\<close> should be generalized
from 2 to \<open>n\<close> and should be made executable. In the end they should be moved
to theory \<open>Log_Nat\<close> and \<open>floorlog\<close> should be replaced.\<close>

lemma floor_log_nat_ivl: fixes b n k :: nat
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

lemma ceil_log_nat_ivl: fixes b n k :: nat
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
  from ceil_log_nat_ivl[OF _ this *] ceil_log_nat_ivl[OF _ i]
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
  from floor_log_nat_ivl[OF _ * this] floor_log_nat_ivl[OF _ i]
  show ?thesis by simp
qed

lemma balanced_Node_if_wbal1:
assumes "balanced l" "balanced r" "size l = size r + 1"
shows "balanced \<langle>l, x, r\<rangle>"
proof -
  from assms(3) have [simp]: "size1 l = size1 r + 1" by(simp add: size1_def)
  have "nat \<lceil>log 2 (1 + size1 r)\<rceil> \<ge> nat \<lceil>log 2 (size1 r)\<rceil>"
    by(rule nat_mono[OF ceiling_mono]) simp
  hence 1: "height(Node l x r) = nat \<lceil>log 2 (1 + size1 r)\<rceil> + 1"
    using height_balanced[OF assms(1)] height_balanced[OF assms(2)]
    by (simp del: nat_ceiling_le_eq add: max_def)
  have "nat \<lfloor>log 2 (1 + size1 r)\<rfloor> \<ge> nat \<lfloor>log 2 (size1 r)\<rfloor>"
    by(rule nat_mono[OF floor_mono]) simp
  hence 2: "min_height(Node l x r) = nat \<lfloor>log 2 (size1 r)\<rfloor> + 1"
    using min_height_balanced[OF assms(1)] min_height_balanced[OF assms(2)]
    by (simp)
  have "size1 r \<ge> 1" by(simp add: size1_def)
  then obtain i where i: "2 ^ i \<le> size1 r" "size1 r < 2 ^ (i + 1)"
    using ex_power_ivl1[of 2 "size1 r"] by auto
  hence i1: "2 ^ i < size1 r + 1" "size1 r + 1 \<le> 2 ^ (i + 1)" by auto
  from 1 2 floor_log_nat_ivl[OF _ i] ceil_log_nat_ivl[OF _ i1]
  show ?thesis by(simp add:balanced_def)
qed

lemma balanced_sym: "balanced \<langle>l, x, r\<rangle> \<Longrightarrow> balanced \<langle>r, y, l\<rangle>"
by(auto simp: balanced_def)

lemma balanced_Node_if_wbal2:
assumes "balanced l" "balanced r" "abs(int(size l) - int(size r)) \<le> 1"
shows "balanced \<langle>l, x, r\<rangle>"
proof -
  have "size l = size r \<or> (size l = size r + 1 \<or> size r = size l + 1)" (is "?A \<or> ?B")
    using assms(3) by linarith
  thus ?thesis
  proof
    assume "?A"
    thus ?thesis using assms(1,2)
      apply(simp add: balanced_def min_def max_def)
      by (metis assms(1,2) balanced_optimal le_antisym le_less)
  next
    assume "?B"
    thus ?thesis
      by (meson assms(1,2) balanced_sym balanced_Node_if_wbal1)
  qed
qed

lemma balanced_if_wbalanced: "wbalanced t \<Longrightarrow> balanced t"
proof(induction t)
  case Leaf show ?case by (simp add: balanced_def)
next
  case (Node l x r)
  thus ?case by(simp add: balanced_Node_if_wbal2)
qed

(* end of mv *)

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
  "bal n xs = (t,ys) \<Longrightarrow> min_height t = nat(floor(log 2 (n + 1)))"
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
      using ceil_log2_div2[of "n+1"] by (simp)
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
  "n \<le> length xs \<Longrightarrow> height (bal_tree n t) = nat(ceiling(log 2 (n + 1)))"
unfolding bal_list_def bal_tree_def
using height_bal prod.exhaust_sel by blast

corollary height_balance_tree:
  "height (balance_tree t) = nat(ceiling(log 2 (size t + 1)))"
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
