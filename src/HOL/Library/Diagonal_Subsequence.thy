(* Author: Fabian Immler, TUM *)

header {* Sequence of Properties on Subsequences *}

theory Diagonal_Subsequence
imports SEQ
begin

locale subseqs =
  fixes P::"nat\<Rightarrow>(nat\<Rightarrow>nat)\<Rightarrow>bool"
  assumes ex_subseq: "\<And>n s. subseq s \<Longrightarrow> \<exists>r'. subseq r' \<and> P n (s o r')"
begin

primrec seqseq where
  "seqseq 0 = id"
| "seqseq (Suc n) = seqseq n o (SOME r'. subseq r' \<and> P n (seqseq n o r'))"

lemma seqseq_ex:
  shows "subseq (seqseq n) \<and>
  (\<exists>r'. seqseq (Suc n) = seqseq n o r' \<and> subseq r' \<and> P n (seqseq n o r'))"
proof (induct n)
  case 0
  let ?P = "\<lambda>r'. subseq r' \<and> P 0 r'"
  let ?r = "Eps ?P"
  have "?P ?r" using ex_subseq[of id 0] by (intro someI_ex[of ?P]) (auto simp: subseq_def)
  thus ?case by (auto simp: subseq_def)
next
  case (Suc n)
  then obtain r' where
    Suc': "seqseq (Suc n) = seqseq n \<circ> r'" "subseq (seqseq n)" "subseq r'"
      "P n (seqseq n o r')"
    by blast
  let ?P = "\<lambda>r'a. subseq (r'a ) \<and> P (Suc n) (seqseq n o r' o r'a)"
  let ?r = "Eps ?P"
  have "?P ?r" using ex_subseq[of "seqseq n o r'" "Suc n"] Suc'
    by (intro someI_ex[of ?P]) (auto intro: subseq_o simp: o_assoc)
  moreover have "seqseq (Suc (Suc n)) = seqseq n \<circ> r' \<circ> ?r"
    by (subst seqseq.simps) (simp only: Suc' o_assoc)
  moreover note subseq_o[OF `subseq (seqseq n)` `subseq r'`]
  ultimately show ?case unfolding Suc' by (auto simp: o_def)
qed

lemma subseq_seqseq:
  shows "subseq (seqseq n)" using seqseq_ex[OF assms] by auto

definition reducer where "reducer n = (SOME r'. subseq r' \<and> P n (seqseq n o r'))"

lemma subseq_reducer: "subseq (reducer n)" and reducer_reduces: "P n (seqseq n o reducer n)"
  unfolding atomize_conj unfolding reducer_def using subseq_seqseq
  by (rule someI_ex[OF ex_subseq])

lemma seqseq_reducer[simp]:
  "seqseq (Suc n) = seqseq n o reducer n"
  by (simp add: reducer_def)

declare seqseq.simps(2)[simp del]

definition diagseq where "diagseq i = seqseq i i"

lemma diagseq_mono: "diagseq n < diagseq (Suc n)"
  unfolding diagseq_def seqseq_reducer o_def
  by (metis subseq_mono[OF subseq_seqseq] less_le_trans lessI seq_suble subseq_reducer)

lemma subseq_diagseq: "subseq diagseq"
  using diagseq_mono by (simp add: subseq_Suc_iff diagseq_def)

primrec fold_reduce where
  "fold_reduce n 0 = id"
| "fold_reduce n (Suc k) = fold_reduce n k o reducer (n + k)"

lemma subseq_fold_reduce: "subseq (fold_reduce n k)"
proof (induct k)
  case (Suc k) from subseq_o[OF this subseq_reducer] show ?case by (simp add: o_def)
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
  by (metis subseq_mono[OF subseq_fold_reduce] less_le_trans lessI add_Suc_right seq_suble
      subseq_reducer)

lemma diagseq_seqseq: "diagseq o (op + k) = (seqseq k o (\<lambda>x. fold_reduce k x (k + x)))"
  by (auto simp: o_def diagseq_add)

end

end
