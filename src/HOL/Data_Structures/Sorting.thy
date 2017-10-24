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

lemma "sorted (insort a xs) = sorted xs"
apply(induction xs)
apply (auto)
oops

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

subsection "Time Complexity"

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

(* We count the number of comparisons between list elements only *)

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

end
