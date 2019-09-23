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

lemma bal_inorder:
  "\<lbrakk> n \<le> length xs; bal n xs = (t,zs) \<rbrakk>
  \<Longrightarrow> inorder t = take n xs \<and> zs = drop n xs"
proof(induction n xs arbitrary: t zs rule: bal.induct)
  case (1 n xs) show ?case
  proof cases
    assume "n = 0" thus ?thesis using 1 by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?m = "n div 2" let ?m' = "n - 1 - ?m"
    from "1.prems"(2) obtain l r ys where
      b1: "bal ?m xs = (l,ys)" and
      b2: "bal ?m' (tl ys) = (r,zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp: Let_def bal_simps split: prod.splits)
    have IH1: "inorder l = take ?m xs \<and> ys = drop ?m xs"
      using b1 "1.prems"(1) by(intro "1.IH"(1)) auto
    have IH2: "inorder r = take ?m' (tl ys) \<and> zs = drop ?m' (tl ys)"
      using b1 b2 IH1 "1.prems"(1) by(intro "1.IH"(2)) auto
    have "drop (n div 2) xs \<noteq> []" using "1.prems"(1) by simp
    hence "hd (drop ?m xs) # take ?m' (tl (drop ?m xs)) = take (?m' + 1) (drop ?m xs)"
      by (metis Suc_eq_plus1 take_Suc)
    hence *: "inorder t = take n xs" using t IH1 IH2
      using take_add[of ?m "?m'+1" xs] by(simp)
    have "n - n div 2 + n div 2 = n" by simp
    hence "zs = drop n xs" using IH1 IH2 by (simp add: drop_Suc[symmetric])
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


text\<open>The size lemmas below do not require the precondition @{prop"n \<le> length xs"}
(or  @{prop"n \<le> size t"}) that they come with. They could take advantage of the fact
that @{term "bal xs n"} yields a result even if @{prop "n > length xs"}.
In that case the result will contain one or more occurrences of @{term "hd []"}.
However, this is counter-intuitive and does not reflect the execution
in an eager functional language.\<close>

lemma size_bal: "\<lbrakk> n \<le> length xs; bal n xs = (t,zs) \<rbrakk> \<Longrightarrow> size t = n \<and> length zs = length xs - n"
by (metis bal_inorder length_drop length_inorder length_take min.absorb2)

corollary size_bal_list[simp]: "n \<le> length xs \<Longrightarrow> size(bal_list n xs) = n"
unfolding bal_list_def by (metis prod.collapse size_bal)

corollary size_balance_list[simp]: "size(balance_list xs) = length xs"
by (simp add: balance_list_def)

corollary size_bal_tree[simp]: "n \<le> size t \<Longrightarrow> size(bal_tree n t) = n"
by(simp add: bal_tree_def)

corollary size_balance_tree[simp]: "size(balance_tree t) = size t"
by(simp add: balance_tree_def)

lemma pre_rec2: "\<lbrakk> n \<le> length xs; bal (n div 2) xs = (l, ys) \<rbrakk>
 \<Longrightarrow> (n - 1 - n div 2) \<le> length(tl ys)"
using size_bal[of "n div 2" xs l ys] by simp

lemma min_height_bal:
  "\<lbrakk> n \<le> length xs; bal n xs = (t,zs) \<rbrakk> \<Longrightarrow> min_height t = nat(\<lfloor>log 2 (n + 1)\<rfloor>)"
proof(induction n xs arbitrary: t zs rule: bal.induct)
  case (1 n xs)
  show ?case
  proof cases
    assume "n = 0" thus ?thesis using "1.prems"(2) by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r ys where
      b1: "bal (n div 2) xs = (l,ys)" and
      b2: "bal (n - 1 - n div 2) (tl ys) = (r,zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp: bal_simps Let_def split: prod.splits)
    let ?log1 = "nat (floor(log 2 (n div 2 + 1)))"
    let ?log2 = "nat (floor(log 2 (n - 1 - n div 2 + 1)))"
    have IH1: "min_height l = ?log1" using "1.IH"(1) b1 "1.prems"(1) by simp
    have IH2: "min_height r = ?log2"
      using "1.prems"(1) size_bal[OF _ b1] size_bal[OF _ b2] b1 b2 by(intro "1.IH"(2)) auto
    have "(n+1) div 2 \<ge> 1" by arith
    hence 0: "log 2 ((n+1) div 2) \<ge> 0" by simp
    have "n - 1 - n div 2 + 1 \<le> n div 2 + 1" by arith
    hence le: "?log2 \<le> ?log1" by(simp add: nat_mono floor_mono)
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
  "\<lbrakk> n \<le> length xs; bal n xs = (t,zs) \<rbrakk> \<Longrightarrow> height t = nat \<lceil>log 2 (n + 1)\<rceil>"
proof(induction n xs arbitrary: t zs rule: bal.induct)
  case (1 n xs) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using "1.prems" by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    from "1.prems" obtain l r ys where
      b1: "bal (n div 2) xs = (l,ys)" and
      b2: "bal (n - 1 - n div 2) (tl ys) = (r,zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp: bal_simps Let_def split: prod.splits)
    let ?log1 = "nat \<lceil>log 2 (n div 2 + 1)\<rceil>"
    let ?log2 = "nat \<lceil>log 2 (n - 1 - n div 2 + 1)\<rceil>"
    have 1: "n div 2 \<le> length xs" using "1.prems"(1) by linarith
    have 2: "n - 1 - n div 2 \<le> length (tl ys)" using "1.prems"(1) size_bal[OF 1 b1] by simp
    have IH1: "height l = ?log1" using "1.IH"(1) b1 "1.prems"(1) by simp
    have IH2: "height r = ?log2"
      using b1 b2 size_bal[OF _ b1] size_bal[OF _ b2] "1.prems"(1) by(intro "1.IH"(2)) auto
    have 0: "log 2 (n div 2 + 1) \<ge> 0" by simp
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
  assumes "n \<le> length xs" "bal n xs = (t,ys)" shows "balanced t"
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
  "n \<le> size t \<Longrightarrow> height (bal_tree n t) = nat\<lceil>log 2 (n + 1)\<rceil>"
unfolding bal_list_def bal_tree_def
by (metis bal_list_def height_bal_list length_inorder)

corollary height_balance_tree:
  "height (balance_tree t) = nat\<lceil>log 2 (size t + 1)\<rceil>"
by (simp add: bal_tree_def balance_tree_def height_bal_list)

corollary balanced_bal_list[simp]: "n \<le> length xs \<Longrightarrow> balanced (bal_list n xs)"
unfolding bal_list_def by (metis  balanced_bal prod.collapse)

corollary balanced_balance_list[simp]: "balanced (balance_list xs)"
by (simp add: balance_list_def)

corollary balanced_bal_tree[simp]: "n \<le> size t \<Longrightarrow> balanced (bal_tree n t)"
by (simp add: bal_tree_def)

corollary balanced_balance_tree[simp]: "balanced (balance_tree t)"
by (simp add: balance_tree_def)

lemma wbalanced_bal: "\<lbrakk> n \<le> length xs; bal n xs = (t,ys) \<rbrakk> \<Longrightarrow> wbalanced t"
proof(induction n xs arbitrary: t ys rule: bal.induct)
  case (1 n xs)
  show ?case
  proof cases
    assume "n = 0"
    thus ?thesis using "1.prems"(2) by(simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    with "1.prems" obtain l ys r zs where
      rec1: "bal (n div 2) xs = (l, ys)" and
      rec2: "bal (n - 1 - n div 2) (tl ys) = (r, zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp add: bal_simps Let_def split: prod.splits)
    have l: "wbalanced l" using "1.IH"(1)[OF \<open>n\<noteq>0\<close> refl _ rec1] "1.prems"(1) by linarith
    have "wbalanced r"
      using rec1 rec2 pre_rec2[OF "1.prems"(1) rec1] by(intro "1.IH"(2)) auto
    with l t size_bal[OF _ rec1] size_bal[OF _ rec2] "1.prems"(1)
    show ?thesis by auto
  qed
qed

text\<open>An alternative proof via @{thm balanced_if_wbalanced}:\<close>
lemma "\<lbrakk> n \<le> length xs; bal n xs = (t,ys) \<rbrakk> \<Longrightarrow> balanced t"
by(rule balanced_if_wbalanced[OF wbalanced_bal])

lemma wbalanced_bal_list[simp]: "n \<le> length xs \<Longrightarrow> wbalanced (bal_list n xs)"
by(simp add: bal_list_def) (metis prod.collapse wbalanced_bal)

lemma wbalanced_balance_list[simp]: "wbalanced (balance_list xs)"
by(simp add: balance_list_def)

lemma wbalanced_bal_tree[simp]: "n \<le> size t \<Longrightarrow> wbalanced (bal_tree n t)"
by(simp add: bal_tree_def)

lemma wbalanced_balance_tree: "wbalanced (balance_tree t)"
by (simp add: balance_tree_def)

hide_const (open) bal

end
