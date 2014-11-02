(* Author: Fabian Immler, TUM *)

section {* Sequence of Properties on Subsequences *}

theory Diagonal_Subsequence
imports Complex_Main
begin

locale subseqs =
  fixes P::"nat\<Rightarrow>(nat\<Rightarrow>nat)\<Rightarrow>bool"
  assumes ex_subseq: "\<And>n s. subseq s \<Longrightarrow> \<exists>r'. subseq r' \<and> P n (s o r')"
begin

definition reduce where "reduce s n = (SOME r'. subseq r' \<and> P n (s o r'))"

lemma subseq_reduce[intro, simp]:
  "subseq s \<Longrightarrow> subseq (reduce s n)"
  unfolding reduce_def by (rule someI2_ex[OF ex_subseq]) auto

lemma reduce_holds:
  "subseq s \<Longrightarrow> P n (s o reduce s n)"
  unfolding reduce_def by (rule someI2_ex[OF ex_subseq]) (auto simp: o_def)

primrec seqseq where
  "seqseq 0 = id"
| "seqseq (Suc n) = seqseq n o reduce (seqseq n) n"

lemma subseq_seqseq[intro, simp]: "subseq (seqseq n)"
proof (induct n)
  case 0 thus ?case by (simp add: subseq_def)
next
  case (Suc n) thus ?case by (subst seqseq.simps) (auto intro!: subseq_o)
qed

lemma seqseq_holds:
  "P n (seqseq (Suc n))"
proof -
  have "P n (seqseq n o reduce (seqseq n) n)"
    by (intro reduce_holds subseq_seqseq)
  thus ?thesis by simp
qed

definition diagseq where "diagseq i = seqseq i i"

lemma subseq_mono: "subseq f \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> f b"
  by (metis le_eq_less_or_eq subseq_mono)

lemma subseq_strict_mono: "subseq f \<Longrightarrow> a < b \<Longrightarrow> f a < f b"
  by (simp add: subseq_def)

lemma diagseq_mono: "diagseq n < diagseq (Suc n)"
proof -
  have "diagseq n < seqseq n (Suc n)"
    using subseq_seqseq[of n] by (simp add: diagseq_def subseq_def)
  also have "\<dots> \<le> seqseq n (reduce (seqseq n) n (Suc n))"
    by (auto intro: subseq_mono seq_suble)
  also have "\<dots> = diagseq (Suc n)" by (simp add: diagseq_def)
  finally show ?thesis .
qed

lemma subseq_diagseq: "subseq diagseq"
  using diagseq_mono by (simp add: subseq_Suc_iff diagseq_def)

primrec fold_reduce where
  "fold_reduce n 0 = id"
| "fold_reduce n (Suc k) = fold_reduce n k o reduce (seqseq (n + k)) (n + k)"

lemma subseq_fold_reduce[intro, simp]: "subseq (fold_reduce n k)"
proof (induct k)
  case (Suc k) from subseq_o[OF this subseq_reduce] show ?case by (simp add: o_def)
qed (simp add: subseq_def)

lemma ex_subseq_reduce_index: "seqseq (n + k) = seqseq n o fold_reduce n k"
  by (induct k) simp_all

lemma seqseq_fold_reduce: "seqseq n = fold_reduce 0 n"
  by (induct n) (simp_all)

lemma diagseq_fold_reduce: "diagseq n = fold_reduce 0 n n"
  using seqseq_fold_reduce by (simp add: diagseq_def)

lemma fold_reduce_add: "fold_reduce 0 (m + n) = fold_reduce 0 m o fold_reduce m n"
  by (induct n) simp_all

lemma diagseq_add: "diagseq (k + n) = (seqseq k o (fold_reduce k n)) (k + n)"
proof -
  have "diagseq (k + n) = fold_reduce 0 (k + n) (k + n)"
    by (simp add: diagseq_fold_reduce)
  also have "\<dots> = (seqseq k o fold_reduce k n) (k + n)"
    unfolding fold_reduce_add seqseq_fold_reduce ..
  finally show ?thesis .
qed

lemma diagseq_sub:
  assumes "m \<le> n" shows "diagseq n = (seqseq m o (fold_reduce m (n - m))) n"
  using diagseq_add[of m "n - m"] assms by simp

lemma subseq_diagonal_rest: "subseq (\<lambda>x. fold_reduce k x (k + x))"
  unfolding subseq_Suc_iff fold_reduce.simps o_def
proof
  fix n
  have "fold_reduce k n (k + n) < fold_reduce k n (k + Suc n)" (is "?lhs < _")
    by (auto intro: subseq_strict_mono)
  also have "\<dots> \<le> fold_reduce k n (reduce (seqseq (k + n)) (k + n) (k + Suc n))"
    by (rule subseq_mono) (auto intro!: seq_suble subseq_mono)
  finally show "?lhs < \<dots>" .
qed

lemma diagseq_seqseq: "diagseq o (op + k) = (seqseq k o (\<lambda>x. fold_reduce k x (k + x)))"
  by (auto simp: o_def diagseq_add)

lemma diagseq_holds:
  assumes subseq_stable: "\<And>r s n. subseq r \<Longrightarrow> P n s \<Longrightarrow> P n (s o r)"
  shows "P k (diagseq o (op + (Suc k)))"
  unfolding diagseq_seqseq by (intro subseq_stable subseq_diagonal_rest seqseq_holds)

end

end
