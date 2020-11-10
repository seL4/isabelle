(* Author: Tobias Nipkow *)

section \<open>Creating Almost Complete Trees\<close>

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
declare Let_def[simp]

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
  \<Longrightarrow> xs = inorder t @ zs \<and> size t = n"
proof(induction n arbitrary: xs t zs rule: less_induct)
  case (less n) show ?case
  proof cases
    assume "n = 0" thus ?thesis using less.prems by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?m = "n div 2" let ?m' = "n - 1 - ?m"
    from less.prems(2) obtain l r ys where
      b1: "bal ?m xs = (l,ys)" and
      b2: "bal ?m' (tl ys) = (r,zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp: bal_simps split: prod.splits)
    have IH1: "xs = inorder l @ ys \<and> size l = ?m"
      using b1 less.prems(1) by(intro less.IH) auto
    have IH2: "tl ys = inorder r @ zs \<and> size r = ?m'"
      using  b2 IH1 less.prems(1) by(intro less.IH) auto
    show ?thesis using t IH1 IH2 less.prems(1) hd_Cons_tl[of ys] by fastforce
  qed
qed

corollary inorder_bal_list[simp]:
  "n \<le> length xs \<Longrightarrow> inorder(bal_list n xs) = take n xs"
unfolding bal_list_def
by (metis (mono_tags) prod.collapse[of "bal n xs"] append_eq_conv_conj bal_inorder length_inorder)

corollary inorder_balance_list[simp]: "inorder(balance_list xs) = xs"
by(simp add: balance_list_def)

corollary inorder_bal_tree:
  "n \<le> size t \<Longrightarrow> inorder(bal_tree n t) = take n (inorder t)"
by(simp add: bal_tree_def)

corollary inorder_balance_tree[simp]: "inorder(balance_tree t) = inorder t"
by(simp add: balance_tree_def inorder_bal_tree)


text\<open>The length/size lemmas below do not require the precondition @{prop"n \<le> length xs"}
(or  @{prop"n \<le> size t"}) that they come with. They could take advantage of the fact
that @{term "bal xs n"} yields a result even if @{prop "n > length xs"}.
In that case the result will contain one or more occurrences of @{term "hd []"}.
However, this is counter-intuitive and does not reflect the execution
in an eager functional language.\<close>

lemma bal_length: "\<lbrakk> n \<le> length xs; bal n xs = (t,zs) \<rbrakk> \<Longrightarrow> length zs = length xs - n"
using bal_inorder by fastforce

corollary size_bal_list[simp]: "n \<le> length xs \<Longrightarrow> size(bal_list n xs) = n"
unfolding bal_list_def using bal_inorder prod.exhaust_sel by blast

corollary size_balance_list[simp]: "size(balance_list xs) = length xs"
by (simp add: balance_list_def)

corollary size_bal_tree[simp]: "n \<le> size t \<Longrightarrow> size(bal_tree n t) = n"
by(simp add: bal_tree_def)

corollary size_balance_tree[simp]: "size(balance_tree t) = size t"
by(simp add: balance_tree_def)

lemma min_height_bal:
  "\<lbrakk> n \<le> length xs; bal n xs = (t,zs) \<rbrakk> \<Longrightarrow> min_height t = nat(\<lfloor>log 2 (n + 1)\<rfloor>)"
proof(induction n arbitrary: xs t zs rule: less_induct)
  case (less n)
  show ?case
  proof cases
    assume "n = 0" thus ?thesis using less.prems(2) by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?m = "n div 2" let ?m' = "n - 1 - ?m"
    from less.prems obtain l r ys where
      b1: "bal ?m xs = (l,ys)" and
      b2: "bal ?m' (tl ys) = (r,zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp: bal_simps split: prod.splits)
    let ?hl = "nat (floor(log 2 (?m + 1)))"
    let ?hr = "nat (floor(log 2 (?m' + 1)))"
    have IH1: "min_height l = ?hl" using less.IH[OF _ _ b1] less.prems(1) by simp
    have IH2: "min_height r = ?hr"
      using less.prems(1) bal_length[OF _ b1] b2 by(intro less.IH) auto
    have "(n+1) div 2 \<ge> 1" by arith
    hence 0: "log 2 ((n+1) div 2) \<ge> 0" by simp
    have "?m' \<le> ?m" by arith
    hence le: "?hr \<le> ?hl" by(simp add: nat_mono floor_mono)
    have "min_height t = min ?hl ?hr + 1" by (simp add: t IH1 IH2)
    also have "\<dots> = ?hr + 1" using le by (simp add: min_absorb2)
    also have "?m' + 1 = (n+1) div 2" by linarith
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
proof(induction n arbitrary: xs t zs rule: less_induct)
  case (less n) show ?case
  proof cases
    assume "n = 0" thus ?thesis
      using less.prems by (simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    let ?m = "n div 2" let ?m' = "n - 1 - ?m"
    from less.prems obtain l r ys where
      b1: "bal ?m xs = (l,ys)" and
      b2: "bal ?m' (tl ys) = (r,zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp: bal_simps split: prod.splits)
    let ?hl = "nat \<lceil>log 2 (?m + 1)\<rceil>"
    let ?hr = "nat \<lceil>log 2 (?m' + 1)\<rceil>"
    have IH1: "height l = ?hl" using less.IH[OF _ _ b1] less.prems(1) by simp
    have IH2: "height r = ?hr"
      using b2 bal_length[OF _ b1] less.prems(1) by(intro less.IH) auto
    have 0: "log 2 (?m + 1) \<ge> 0" by simp
    have "?m' \<le> ?m" by arith
    hence le: "?hr \<le> ?hl"
      by(simp add: nat_mono ceiling_mono del: nat_ceiling_le_eq)
    have "height t = max ?hl ?hr + 1" by (simp add: t IH1 IH2)
    also have "\<dots> = ?hl + 1" using le by (simp add: max_absorb1)
    also have "\<dots> = nat \<lceil>log 2 (?m + 1) + 1\<rceil>" using 0 by linarith
    also have "\<dots> = nat \<lceil>log 2 (n + 1)\<rceil>"
      using ceiling_log2_div2[of "n+1"] by (simp)
    finally show ?thesis .
  qed
qed

lemma acomplete_bal:
  assumes "n \<le> length xs" "bal n xs = (t,ys)" shows "acomplete t"
unfolding acomplete_def
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

corollary acomplete_bal_list[simp]: "n \<le> length xs \<Longrightarrow> acomplete (bal_list n xs)"
unfolding bal_list_def by (metis  acomplete_bal prod.collapse)

corollary acomplete_balance_list[simp]: "acomplete (balance_list xs)"
by (simp add: balance_list_def)

corollary acomplete_bal_tree[simp]: "n \<le> size t \<Longrightarrow> acomplete (bal_tree n t)"
by (simp add: bal_tree_def)

corollary acomplete_balance_tree[simp]: "acomplete (balance_tree t)"
by (simp add: balance_tree_def)

lemma wbalanced_bal: "\<lbrakk> n \<le> length xs; bal n xs = (t,ys) \<rbrakk> \<Longrightarrow> wbalanced t"
proof(induction n arbitrary: xs t ys rule: less_induct)
  case (less n)
  show ?case
  proof cases
    assume "n = 0"
    thus ?thesis using less.prems(2) by(simp add: bal_simps)
  next
    assume [arith]: "n \<noteq> 0"
    with less.prems obtain l ys r zs where
      rec1: "bal (n div 2) xs = (l, ys)" and
      rec2: "bal (n - 1 - n div 2) (tl ys) = (r, zs)" and
      t: "t = \<langle>l, hd ys, r\<rangle>"
      by(auto simp add: bal_simps split: prod.splits)
    have l: "wbalanced l" using less.IH[OF _ _ rec1] less.prems(1) by linarith
    have "wbalanced r"
      using rec1 rec2 bal_length[OF _ rec1] less.prems(1) by(intro less.IH) auto
    with l t bal_length[OF _ rec1] less.prems(1) bal_inorder[OF _ rec1] bal_inorder[OF _ rec2]
    show ?thesis by auto
  qed
qed

text\<open>An alternative proof via @{thm acomplete_if_wbalanced}:\<close>
lemma "\<lbrakk> n \<le> length xs; bal n xs = (t,ys) \<rbrakk> \<Longrightarrow> acomplete t"
by(rule acomplete_if_wbalanced[OF wbalanced_bal])

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
