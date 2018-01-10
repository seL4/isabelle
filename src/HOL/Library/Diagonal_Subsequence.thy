(* Author: Fabian Immler, TUM *)

section \<open>Sequence of Properties on Subsequences\<close>

theory Diagonal_Subsequence
imports Complex_Main
begin

locale subseqs =
  fixes P::"nat\<Rightarrow>(nat\<Rightarrow>nat)\<Rightarrow>bool"
  assumes ex_subseq: "\<And>n s. strict_mono (s::nat\<Rightarrow>nat) \<Longrightarrow> \<exists>r'. strict_mono r' \<and> P n (s \<circ> r')"
begin

definition reduce where "reduce s n = (SOME r'::nat\<Rightarrow>nat. strict_mono r' \<and> P n (s \<circ> r'))"

lemma subseq_reduce[intro, simp]:
  "strict_mono s \<Longrightarrow> strict_mono (reduce s n)"
  unfolding reduce_def by (rule someI2_ex[OF ex_subseq]) auto

lemma reduce_holds:
  "strict_mono s \<Longrightarrow> P n (s \<circ> reduce s n)"
  unfolding reduce_def by (rule someI2_ex[OF ex_subseq]) (auto simp: o_def)

primrec seqseq :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "seqseq 0 = id"
| "seqseq (Suc n) = seqseq n \<circ> reduce (seqseq n) n"

lemma subseq_seqseq[intro, simp]: "strict_mono (seqseq n)"
proof (induct n)
  case 0 thus ?case by (simp add: strict_mono_def)
next
  case (Suc n) thus ?case by (subst seqseq.simps) (auto intro!: strict_mono_o)
qed

lemma seqseq_holds:
  "P n (seqseq (Suc n))"
proof -
  have "P n (seqseq n \<circ> reduce (seqseq n) n)"
    by (intro reduce_holds subseq_seqseq)
  thus ?thesis by simp
qed

definition diagseq :: "nat \<Rightarrow> nat" where "diagseq i = seqseq i i"

lemma diagseq_mono: "diagseq n < diagseq (Suc n)"
proof -
  have "diagseq n < seqseq n (Suc n)"
    using subseq_seqseq[of n] by (simp add: diagseq_def strict_mono_def)
  also have "\<dots> \<le> seqseq n (reduce (seqseq n) n (Suc n))"
    using strict_mono_less_eq seq_suble by blast
  also have "\<dots> = diagseq (Suc n)" by (simp add: diagseq_def)
  finally show ?thesis .
qed

lemma subseq_diagseq: "strict_mono diagseq"
  using diagseq_mono by (simp add: strict_mono_Suc_iff diagseq_def)

primrec fold_reduce where
  "fold_reduce n 0 = id"
| "fold_reduce n (Suc k) = fold_reduce n k \<circ> reduce (seqseq (n + k)) (n + k)"

lemma subseq_fold_reduce[intro, simp]: "strict_mono (fold_reduce n k)"
proof (induct k)
  case (Suc k) from strict_mono_o[OF this subseq_reduce] show ?case by (simp add: o_def)
qed (simp add: strict_mono_def)

lemma ex_subseq_reduce_index: "seqseq (n + k) = seqseq n \<circ> fold_reduce n k"
  by (induct k) simp_all

lemma seqseq_fold_reduce: "seqseq n = fold_reduce 0 n"
  by (induct n) (simp_all)

lemma diagseq_fold_reduce: "diagseq n = fold_reduce 0 n n"
  using seqseq_fold_reduce by (simp add: diagseq_def)

lemma fold_reduce_add: "fold_reduce 0 (m + n) = fold_reduce 0 m \<circ> fold_reduce m n"
  by (induct n) simp_all

lemma diagseq_add: "diagseq (k + n) = (seqseq k \<circ> (fold_reduce k n)) (k + n)"
proof -
  have "diagseq (k + n) = fold_reduce 0 (k + n) (k + n)"
    by (simp add: diagseq_fold_reduce)
  also have "\<dots> = (seqseq k \<circ> fold_reduce k n) (k + n)"
    unfolding fold_reduce_add seqseq_fold_reduce ..
  finally show ?thesis .
qed

lemma diagseq_sub:
  assumes "m \<le> n" shows "diagseq n = (seqseq m \<circ> (fold_reduce m (n - m))) n"
  using diagseq_add[of m "n - m"] assms by simp

lemma subseq_diagonal_rest: "strict_mono (\<lambda>x. fold_reduce k x (k + x))"
  unfolding strict_mono_Suc_iff fold_reduce.simps o_def
proof
  fix n
  have "fold_reduce k n (k + n) < fold_reduce k n (k + Suc n)" (is "?lhs < _")
    by (auto intro: strict_monoD)
  also have "\<dots> \<le> fold_reduce k n (reduce (seqseq (k + n)) (k + n) (k + Suc n))"
    by (auto intro: less_mono_imp_le_mono seq_suble strict_monoD)
  finally show "?lhs < \<dots>" .
qed

lemma diagseq_seqseq: "diagseq \<circ> ((+) k) = (seqseq k \<circ> (\<lambda>x. fold_reduce k x (k + x)))"
  by (auto simp: o_def diagseq_add)

lemma diagseq_holds:
  assumes subseq_stable: "\<And>r s n. strict_mono r \<Longrightarrow> P n s \<Longrightarrow> P n (s \<circ> r)"
  shows "P k (diagseq \<circ> ((+) (Suc k)))"
  unfolding diagseq_seqseq by (intro subseq_stable subseq_diagonal_rest seqseq_holds)

end

end
