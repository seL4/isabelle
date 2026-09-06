section \<open>Relabelling Symmetric Groups along a Bijection\<close>

theory Symmetric_Relabel
  imports Symmetric_Group
begin

text \<open>Relabelling along a bijection @{term e} from @{term "{0..<n}"} to a finite set @{term X}
  transports the symmetric group on @{term X} to @{term "Sn n"}.\<close>

definition pull :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> nat)"
  where "pull n e a = (\<lambda>i. if i < n then inv_into {0..<n} e (a (e i)) else i)"

context
  fixes n :: nat and e :: "nat \<Rightarrow> 'a" and X :: "'a set"
  assumes ebij: "bij_betw e {0..<n} X"
begin

lemma e_in_X: "i < n \<Longrightarrow> e i \<in> X"
  using ebij by (auto simp: bij_betw_def)

lemma inv_e_lt: "x \<in> X \<Longrightarrow> inv_into {0..<n} e x < n"
  using ebij by (metis atLeastLessThan_iff bij_betw_def inv_into_into)

lemma inv_e_e: "i < n \<Longrightarrow> inv_into {0..<n} e (e i) = i"
  using ebij by (simp add: bij_betw_inv_into_left)

lemma e_inv_e: "x \<in> X \<Longrightarrow> e (inv_into {0..<n} e x) = x"
  using ebij by (simp add: bij_betw_inv_into_right)

lemma pull_permutes:
  assumes a: "a \<in> transformations.Sym X"
  shows "pull n e a permutes {0..<n}"
proof (rule bij_imp_permutes)
  have abij: "bij_betw a X X" using a by (simp add: transformations.Units_bijective)
  show "bij_betw (pull n e a) {0..<n} {0..<n}"
  proof (rule bij_betwI)
    show "pull n e a \<in> {0..<n} \<rightarrow> {0..<n}"
      using abij by (auto simp: pull_def e_in_X inv_e_lt bij_betwE)
    show "(\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) \<in> {0..<n} \<rightarrow> {0..<n}"
      using abij by (simp add: bij_betw_def e_in_X inv_e_lt inv_into_into)
  next
    fix i assume "i \<in> {0..<n}"
    then have iln: "i < n" by simp
    have eiX: "e i \<in> X" using iln by (rule e_in_X)
    have aeiX: "a (e i) \<in> X" using abij eiX by (auto simp: bij_betwE)
    have "(\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) (pull n e a i)
            = inv_into {0..<n} e (inv_into X a (e (inv_into {0..<n} e (a (e i)))))"
      using iln by (simp add: pull_def)
    also have "inv_into X a (e (inv_into {0..<n} e (a (e i)))) = e i"
      using abij eiX by (simp add: aeiX bij_betw_inv_into_left e_inv_e)
    finally show "(\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) (pull n e a i) = i"
      by (simp add: iln inv_e_e)
    have inv_in: "inv_into X a (e i) \<in> X"
      using abij eiX by (metis bij_betw_inv_into bij_betwE)
    have "pull n e a ((\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) i)
            = inv_into {0..<n} e (a (e (inv_into {0..<n} e (inv_into X a (e i)))))"
      using iln inv_in by (simp add: pull_def inv_e_lt)
    also have "a (e (inv_into {0..<n} e (inv_into X a (e i)))) = e i"
      by (metis abij bij_betw_inv_into_right e_inv_e eiX inv_in)
    finally show "pull n e a ((\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) i) = i"
      using iln inv_e_e by presburger
  qed
qed (simp add: pull_def)


lemma pull_compose:
  assumes a: "a \<in> transformations.Sym X" and b: "b \<in> transformations.Sym X"
  shows "pull n e (compose X a b) = pull n e a \<circ> pull n e b"
proof (rule ext)
  fix i
  show "pull n e (compose X a b) i = (pull n e a \<circ> pull n e b) i"
  proof (cases "i < n")
    case True
    then have beiX: "b (e i) \<in> X"
      by (meson b bij_betwE e_in_X transformations.Units_bij_betwI)
    then show ?thesis
      using True inv_e_lt beiX by (simp add: True compose_eq e_in_X pull_def e_inv_e)
  next
    case False
    then show ?thesis by (simp add: pull_def compose_def)
  qed
qed

lemma pull_unit: "pull n e (identity X) = id"
  using e_in_X by (auto simp: pull_def inv_e_e)

lemma pull_in_Sn: "a \<in> transformations.Sym X \<Longrightarrow> pull n e a \<in> Sn n"
  by (simp add: Sn_def pull_permutes)

end

end
