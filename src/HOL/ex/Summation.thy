(* Author: Florian Haftmann, TU Muenchen *)

header {* Some basic facts about discrete summation *}

theory Summation
imports Main
begin

text {* Auxiliary. *}

lemma add_setsum_orient:
  "setsum f {k..<j} + setsum f {l..<k} = setsum f {l..<k} + setsum f {k..<j}"
  by (fact plus.commute)

lemma add_setsum_int:
  fixes j k l :: int
  shows "j < k \<Longrightarrow> k < l \<Longrightarrow> setsum f {j..<k} + setsum f {k..<l} = setsum f {j..<l}"
  by (simp_all add: setsum_Un_Int [symmetric] ivl_disj_un)

text {* The shift operator. *}

definition \<Delta> :: "(int \<Rightarrow> 'a\<Colon>ab_group_add) \<Rightarrow> int \<Rightarrow> 'a" where
  "\<Delta> f k = f (k + 1) - f k"

lemma \<Delta>_shift:
  "\<Delta> (\<lambda>k. l + f k) = \<Delta> f"
  by (simp add: \<Delta>_def expand_fun_eq)

lemma \<Delta>_same_shift:
  assumes "\<Delta> f = \<Delta> g"
  shows "\<exists>l. (op +) l \<circ> f = g"
proof -
  fix k
  from assms have "\<And>k. \<Delta> f k = \<Delta> g k" by simp
  then have k_incr: "\<And>k. f (k + 1) - g (k + 1) = f k - g k"
    by (simp add: \<Delta>_def algebra_simps)
  then have "\<And>k. f ((k - 1) + 1) - g ((k - 1) + 1) = f (k - 1) - g (k - 1)"
    by blast
  then have k_decr: "\<And>k. f (k - 1) - g (k - 1) = f k - g k"
    by simp
  have "\<And>k. f k - g k = f 0 - g 0"
  proof -
    fix k
    show "f k - g k = f 0 - g 0"
      by (induct k rule: int_induct) (simp_all add: k_incr k_decr)
  qed
  then have "\<And>k. ((op +) (g 0 - f 0) \<circ> f) k = g k"
    by (simp add: algebra_simps)
  then have "(op +) (g 0 - f 0) \<circ> f = g" ..
  then show ?thesis ..
qed

text {* The formal sum operator. *}

definition \<Sigma> :: "(int \<Rightarrow> 'a\<Colon>ab_group_add) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a" where
  "\<Sigma> f j l = (if j < l then setsum f {j..<l}
    else if j > l then - setsum f {l..<j}
    else 0)"

lemma \<Sigma>_same [simp]:
  "\<Sigma> f j j = 0"
  by (simp add: \<Sigma>_def)

lemma \<Sigma>_positive:
  "j < l \<Longrightarrow> \<Sigma> f j l = setsum f {j..<l}"
  by (simp add: \<Sigma>_def)

lemma \<Sigma>_negative:
  "j > l \<Longrightarrow> \<Sigma> f j l = - \<Sigma> f l j"
  by (simp add: \<Sigma>_def)

lemma add_\<Sigma>:
  "\<Sigma> f j k + \<Sigma> f k l = \<Sigma> f j l"
  by (simp add: \<Sigma>_def algebra_simps add_setsum_int)
   (simp_all add: add_setsum_orient [of f k j l]
      add_setsum_orient [of f j l k]
      add_setsum_orient [of f j k l] add_setsum_int)

lemma \<Sigma>_incr_upper:
  "\<Sigma> f j (l + 1) = \<Sigma> f j l + f l"
proof -
  have "{l..<l+1} = {l}" by auto
  then have "\<Sigma> f l (l + 1) = f l" by (simp add: \<Sigma>_def)
  moreover have "\<Sigma> f j (l + 1) = \<Sigma> f j l + \<Sigma> f l (l + 1)" by (simp add: add_\<Sigma>)
  ultimately show ?thesis by simp
qed

text {* Fundamental lemmas: The relation between @{term \<Delta>} and @{term \<Sigma>}. *}

lemma \<Delta>_\<Sigma>:
  "\<Delta> (\<Sigma> f j) = f"
proof
  fix k
  show "\<Delta> (\<Sigma> f j) k = f k"
    by (simp add: \<Delta>_def \<Sigma>_incr_upper)
qed

lemma \<Sigma>_\<Delta>:
  "\<Sigma> (\<Delta> f) j l = f l - f j"
proof -
  from \<Delta>_\<Sigma> have "\<Delta> (\<Sigma> (\<Delta> f) j) = \<Delta> f" .
  then obtain k where "(op +) k \<circ> \<Sigma> (\<Delta> f) j = f" by (blast dest: \<Delta>_same_shift)
  then have "\<And>q. f q = k + \<Sigma> (\<Delta> f) j q" by (simp add: expand_fun_eq)
  then show ?thesis by simp
qed

end
