(* Author: Tobias Nipkow *)

(* FIXME adjust List.sorted to work like below; [code] is different! *)

theory Sorting
imports
  Complex_Main
  "HOL-Library.Multiset"
begin

hide_const List.sorted List.insort

declare Let_def [simp]

fun sorted :: "'a::linorder list \<Rightarrow> bool" where
"sorted [] = True" |
"sorted (x # xs) = ((\<forall>y\<in>set xs. x \<le> y) & sorted xs)"

lemma sorted_append:
  "sorted (xs@ys) = (sorted xs & sorted ys & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. x\<le>y))"
by (induct xs) (auto)

lemma sorted01: "length xs \<le> 1 \<Longrightarrow> sorted xs"
by(auto simp: le_Suc_eq length_Suc_conv)


subsection "Insertion Sort"

fun insort :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insort x [] = [x]" |
"insort x (y#ys) =
  (if x \<le> y then x#y#ys else y#(insort x ys))"

fun isort :: "'a::linorder list \<Rightarrow> 'a list" where
"isort [] = []" |
"isort (x#xs) = insort x (isort xs)"


subsubsection "Functional Correctness"

lemma mset_insort: "mset (insort x xs) = add_mset x (mset xs)"
apply(induction xs)
apply auto
done

lemma mset_isort: "mset (isort xs) = mset xs"
apply(induction xs)
apply simp
apply (simp add: mset_insort)
done

lemma set_insort: "set (insort x xs) = insert x (set xs)"
by (metis mset_insort set_mset_add_mset_insert set_mset_mset)

lemma set_isort: "set (isort xs) = set xs"
by (metis mset_isort set_mset_mset)

lemma sorted_insort: "sorted (insort a xs) = sorted xs"
apply(induction xs)
apply(auto simp add: set_insort)
done

lemma "sorted (isort xs)"
apply(induction xs)
apply(auto simp: sorted_insort)
done


subsubsection "Time Complexity"

text \<open>We count the number of function calls.\<close>

text\<open>
\<open>insort x [] = [x]\<close>
\<open>insort x (y#ys) =
  (if x \<le> y then x#y#ys else y#(insort x ys))\<close>
\<close>
fun t_insort :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> nat" where
"t_insort x [] = 1" |
"t_insort x (y#ys) =
  (if x \<le> y then 0 else t_insort x ys) + 1"

text\<open>
\<open>isort [] = []\<close>
\<open>isort (x#xs) = insort x (isort xs)\<close>
\<close>
fun t_isort :: "'a::linorder list \<Rightarrow> nat" where
"t_isort [] = 1" |
"t_isort (x#xs) = t_isort xs + t_insort x (isort xs) + 1"


lemma t_insort_length: "t_insort x xs \<le> length xs + 1"
apply(induction xs)
apply auto
done

lemma length_insort: "length (insort x xs) = length xs + 1"
apply(induction xs)
apply auto
done

lemma length_isort: "length (isort xs) = length xs"
apply(induction xs)
apply (auto simp: length_insort)
done

lemma t_isort_length: "t_isort xs \<le> (length xs + 1) ^ 2"
proof(induction xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have "t_isort (x#xs) = t_isort xs + t_insort x (isort xs) + 1" by simp
  also have "\<dots> \<le> (length xs + 1) ^ 2 + t_insort x (isort xs) + 1"
    using Cons.IH by simp
  also have "\<dots> \<le> (length xs + 1) ^ 2 + length xs + 1 + 1"
    using t_insort_length[of x "isort xs"] by (simp add: length_isort)
  also have "\<dots> \<le> (length(x#xs) + 1) ^ 2"
    by (simp add: power2_eq_square)
  finally show ?case .
qed


subsection "Merge Sort"

fun merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"merge [] ys = ys" |
"merge xs [] = xs" |
"merge (x#xs) (y#ys) = (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"

fun msort :: "'a::linorder list \<Rightarrow> 'a list" where
"msort xs = (let n = length xs in
  if n \<le> 1 then xs
  else merge (msort (take (n div 2) xs)) (msort (drop (n div 2) xs)))"

declare msort.simps [simp del]


subsubsection "Functional Correctness"

lemma mset_merge: "mset(merge xs ys) = mset xs + mset ys"
by(induction xs ys rule: merge.induct) auto

lemma "mset (msort xs) = mset xs"
proof(induction xs rule: msort.induct)
  case (1 xs)
  let ?n = "length xs"
  let ?xs1 = "take (?n div 2) xs"
  let ?xs2 = "drop (?n div 2) xs"
  show ?case
  proof cases
    assume "?n \<le> 1"
    thus ?thesis by(simp add: msort.simps[of xs])
  next
    assume "\<not> ?n \<le> 1"
    hence "mset (msort xs) = mset (msort ?xs1) + mset (msort ?xs2)"
      by(simp add: msort.simps[of xs] mset_merge)
    also have "\<dots> = mset ?xs1 + mset ?xs2"
      using \<open>\<not> ?n \<le> 1\<close> by(simp add: "1.IH")
    also have "\<dots> = mset (?xs1 @ ?xs2)" by (simp del: append_take_drop_id)
    also have "\<dots> = mset xs" by simp
    finally show ?thesis .
  qed
qed

lemma set_merge: "set(merge xs ys) = set xs \<union> set ys"
by(induction xs ys rule: merge.induct) (auto)

lemma sorted_merge: "sorted (merge xs ys) \<longleftrightarrow> (sorted xs \<and> sorted ys)"
by(induction xs ys rule: merge.induct) (auto simp: set_merge)

lemma "sorted (msort xs)"
proof(induction xs rule: msort.induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof cases
    assume "?n \<le> 1"
    thus ?thesis by(simp add: msort.simps[of xs] sorted01)
  next
    assume "\<not> ?n \<le> 1"
    thus ?thesis using "1.IH"
      by(simp add: sorted_merge  msort.simps[of xs] mset_merge)
  qed
qed


subsubsection "Time Complexity"

text \<open>We only count the number of comparisons between list elements.\<close>

fun c_merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> nat" where
"c_merge [] ys = 0" |
"c_merge xs [] = 0" |
"c_merge (x#xs) (y#ys) = 1 + (if x \<le> y then c_merge xs (y#ys) else c_merge (x#xs) ys)"

lemma c_merge_ub: "c_merge xs ys \<le> length xs + length ys"
by (induction xs ys rule: c_merge.induct) auto

fun c_msort :: "'a::linorder list \<Rightarrow> nat" where
"c_msort xs =
  (let n = length xs;
       ys = take (n div 2) xs;
       zs = drop (n div 2) xs
   in if n \<le> 1 then 0
      else c_msort ys + c_msort zs + c_merge (msort ys) (msort zs))"

declare c_msort.simps [simp del]

lemma length_merge: "length(merge xs ys) = length xs + length ys"
apply (induction xs ys rule: merge.induct)
apply auto
done

lemma length_msort: "length(msort xs) = length xs"
proof (induction xs rule: msort.induct)
  case (1 xs)
  thus ?case by (auto simp: msort.simps[of xs] length_merge)
qed
text \<open>Why structured proof?
   To have the name "xs" to specialize msort.simps with xs
   to ensure that msort.simps cannot be used recursively.
Also works without this precaution, but that is just luck.\<close>

lemma c_msort_le: "length xs = 2^k \<Longrightarrow> c_msort xs \<le> k * 2^k"
proof(induction k arbitrary: xs)
  case 0 thus ?case by (simp add: c_msort.simps)
next
  case (Suc k)
  let ?n = "length xs"
  let ?ys = "take (?n div 2) xs"
  let ?zs = "drop (?n div 2) xs"
  show ?case
  proof (cases "?n \<le> 1")
    case True
    thus ?thesis by(simp add: c_msort.simps)
  next
    case False
    have "c_msort(xs) =
      c_msort ?ys + c_msort ?zs + c_merge (msort ?ys) (msort ?zs)"
      by (simp add: c_msort.simps msort.simps)
    also have "\<dots> \<le> c_msort ?ys + c_msort ?zs + length ?ys + length ?zs"
      using c_merge_ub[of "msort ?ys" "msort ?zs"] length_msort[of ?ys] length_msort[of ?zs]
      by arith
    also have "\<dots> \<le> k * 2^k + c_msort ?zs + length ?ys + length ?zs"
      using Suc.IH[of ?ys] Suc.prems by simp
    also have "\<dots> \<le> k * 2^k + k * 2^k + length ?ys + length ?zs"
      using Suc.IH[of ?zs] Suc.prems by simp
    also have "\<dots> = 2 * k * 2^k + 2 * 2 ^ k"
      using Suc.prems by simp
    finally show ?thesis by simp
  qed
qed

(* Beware of conversions: *)
lemma "length xs = 2^k \<Longrightarrow> c_msort xs \<le> length xs * log 2 (length xs)"
using c_msort_le[of xs k] apply (simp add: log_nat_power algebra_simps)
by (metis (mono_tags) numeral_power_eq_of_nat_cancel_iff of_nat_le_iff of_nat_mult)


subsection "Bottom-Up Merge Sort"

(* Exercise: make tail recursive *)
fun merge_adj :: "('a::linorder) list list \<Rightarrow> 'a list list" where
"merge_adj [] = []" |
"merge_adj [xs] = [xs]" |
"merge_adj (xs # ys # zss) = merge xs ys # merge_adj zss"

text \<open>For the termination proof of \<open>merge_all\<close> below.\<close>
lemma length_merge_adjacent[simp]: "length (merge_adj xs) = (length xs + 1) div 2"
by (induction xs rule: merge_adj.induct) auto

fun merge_all :: "('a::linorder) list list \<Rightarrow> 'a list" where
"merge_all [] = undefined" |
"merge_all [xs] = xs" |
"merge_all xss = merge_all (merge_adj xss)"

definition msort_bu :: "('a::linorder) list \<Rightarrow> 'a list" where
"msort_bu xs = (if xs = [] then [] else merge_all (map (\<lambda>x. [x]) xs))"


subsubsection "Functional Correctness"

lemma mset_merge_adj:
  "\<Union># image_mset mset (mset (merge_adj xss)) = \<Union># image_mset mset (mset xss)"
by(induction xss rule: merge_adj.induct) (auto simp: mset_merge)

lemma msec_merge_all:
  "xss \<noteq> [] \<Longrightarrow> mset (merge_all xss) = (\<Union># (mset (map mset xss)))"
by(induction xss rule: merge_all.induct) (auto simp: mset_merge mset_merge_adj)

lemma sorted_merge_adj:
  "\<forall>xs \<in> set xss. sorted xs \<Longrightarrow> \<forall>xs \<in> set (merge_adj xss). sorted xs"
by(induction xss rule: merge_adj.induct) (auto simp: sorted_merge)

lemma sorted_merge_all:
  "\<forall>xs \<in> set xss. sorted xs \<Longrightarrow> xss \<noteq> [] \<Longrightarrow> sorted (merge_all xss)"
apply(induction xss rule: merge_all.induct)
using [[simp_depth_limit=3]] by (auto simp add: sorted_merge_adj)

lemma sorted_msort_bu: "sorted (msort_bu xs)"
by(simp add: msort_bu_def sorted_merge_all)

lemma mset_msort: "mset (msort_bu xs) = mset xs"
by(simp add: msort_bu_def msec_merge_all comp_def)


subsubsection "Time Complexity"

fun c_merge_adj :: "('a::linorder) list list \<Rightarrow> real" where
"c_merge_adj [] = 0" |
"c_merge_adj [x] = 0" |
"c_merge_adj (x # y # zs) = c_merge x y + c_merge_adj zs"

fun c_merge_all :: "('a::linorder) list list \<Rightarrow> real" where
"c_merge_all [] = 0" |
"c_merge_all [x] = 0" |
"c_merge_all xs = c_merge_adj xs + c_merge_all (merge_adj xs)"

definition c_msort_bu :: "('a::linorder) list \<Rightarrow> real" where
"c_msort_bu xs = (if xs = [] then 0 else c_merge_all (map (\<lambda>x. [x]) xs))"

lemma length_merge_adj:
  "\<lbrakk> even(length xs); \<forall>x \<in> set xs. length x = m \<rbrakk> \<Longrightarrow> \<forall>x \<in> set (merge_adj xs). length x = 2*m"
by(induction xs rule: merge_adj.induct) (auto simp: length_merge)

lemma c_merge_adj: "\<forall>x \<in> set xs. length x = m \<Longrightarrow> c_merge_adj xs \<le> m * length xs"
proof(induction xs rule: c_merge_adj.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 x y) thus ?case using c_merge_ub[of x y] by (simp add: algebra_simps)
qed

lemma c_merge_all: "\<lbrakk> \<forall>x \<in> set xs. length x = m; length xs = 2^k \<rbrakk>
  \<Longrightarrow> c_merge_all xs \<le> m * k * 2^k"
proof (induction xs arbitrary: k m rule: c_merge_all.induct)
  case 1 thus ?case by simp
next
  case (2 x)
  then show ?case by (simp)
next
  case (3 x y xs)
  let ?xs = "x # y # xs"
  let ?xs2 = "merge_adj ?xs"
  obtain k' where k': "k = Suc k'" using "3.prems"(2)
    by (metis length_Cons nat.inject nat_power_eq_Suc_0_iff nat.exhaust)
  have "even (length xs)" using "3.prems"(2) even_Suc_Suc_iff by fastforce
  from "3.prems"(1) length_merge_adj[OF this]
  have 2: "\<forall>x \<in> set(merge_adj ?xs). length x = 2*m" by(auto simp: length_merge)
  have 3: "length ?xs2 = 2 ^ k'" using "3.prems"(2) k' by auto
  have 4: "length ?xs div 2 = 2 ^ k'"
    using "3.prems"(2) k' by(simp add: power_eq_if[of 2 k] split: if_splits)
  have "c_merge_all ?xs = c_merge_adj ?xs + c_merge_all ?xs2" by simp
  also have "\<dots> \<le> m * 2^k + c_merge_all ?xs2"
    using "3.prems"(2) c_merge_adj[OF "3.prems"(1)] by (auto simp: algebra_simps)
  also have "\<dots> \<le> m * 2^k + (2*m) * k' * 2^k'"
    using "3.IH"[OF 2 3] by simp
  also have "\<dots> = m * k * 2^k"
    using k' by (simp add: algebra_simps)
  finally show ?case .
qed

corollary c_msort_bu: "length xs = 2 ^ k \<Longrightarrow> c_msort_bu xs \<le> k * 2 ^ k"
using c_merge_all[of "map (\<lambda>x. [x]) xs" 1] by (simp add: c_msort_bu_def)

end
