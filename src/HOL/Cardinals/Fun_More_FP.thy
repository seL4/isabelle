(*  Title:      HOL/Cardinals/Fun_More_FP.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

More on injections, bijections and inverses (FP).
*)

header {* More on Injections, Bijections and Inverses (FP) *}

theory Fun_More_FP
imports Hilbert_Choice
begin


text {* This section proves more facts (additional to those in @{text "Fun.thy"},
@{text "Hilbert_Choice.thy"}, and @{text "Finite_Set.thy"}),
mainly concerning injections, bijections, inverses and (numeric) cardinals of
finite sets. *}


subsection {* Properties involving finite and infinite sets *}


lemma inj_on_finite:
assumes "inj_on f A" "f ` A \<le> B" "finite B"
shows "finite A"
using assms by (metis finite_imageD finite_subset)


lemma infinite_imp_bij_betw:
assumes INF: "\<not> finite A"
shows "\<exists>h. bij_betw h A (A - {a})"
proof(cases "a \<in> A")
  assume Case1: "a \<notin> A"  hence "A - {a} = A" by blast
  thus ?thesis using bij_betw_id[of A] by auto
next
  assume Case2: "a \<in> A"
find_theorems "\<not> finite _"
  have "\<not> finite (A - {a})" using INF by auto
  with infinite_iff_countable_subset[of "A - {a}"] obtain f::"nat \<Rightarrow> 'a"
  where 1: "inj f" and 2: "f ` UNIV \<le> A - {a}" by blast
  obtain g where g_def: "g = (\<lambda> n. if n = 0 then a else f (Suc n))" by blast
  obtain A' where A'_def: "A' = g ` UNIV" by blast
  have temp: "\<forall>y. f y \<noteq> a" using 2 by blast
  have 3: "inj_on g UNIV \<and> g ` UNIV \<le> A \<and> a \<in> g ` UNIV"
  proof(auto simp add: Case2 g_def, unfold inj_on_def, intro ballI impI,
        case_tac "x = 0", auto simp add: 2)
    fix y  assume "a = (if y = 0 then a else f (Suc y))"
    thus "y = 0" using temp by (case_tac "y = 0", auto)
  next
    fix x y
    assume "f (Suc x) = (if y = 0 then a else f (Suc y))"
    thus "x = y" using 1 temp unfolding inj_on_def by (case_tac "y = 0", auto)
  next
    fix n show "f (Suc n) \<in> A" using 2 by blast
  qed
  hence 4: "bij_betw g UNIV A' \<and> a \<in> A' \<and> A' \<le> A"
  using inj_on_imp_bij_betw[of g] unfolding A'_def by auto
  hence 5: "bij_betw (inv g) A' UNIV"
  by (auto simp add: bij_betw_inv_into)
  (*  *)
  obtain n where "g n = a" using 3 by auto
  hence 6: "bij_betw g (UNIV - {n}) (A' - {a})"
  using 3 4 unfolding A'_def
  by clarify (rule bij_betw_subset, auto simp: image_set_diff)
  (*  *)
  obtain v where v_def: "v = (\<lambda> m. if m < n then m else Suc m)" by blast
  have 7: "bij_betw v UNIV (UNIV - {n})"
  proof(unfold bij_betw_def inj_on_def, intro conjI, clarify)
    fix m1 m2 assume "v m1 = v m2"
    thus "m1 = m2"
    by(case_tac "m1 < n", case_tac "m2 < n",
       auto simp add: inj_on_def v_def, case_tac "m2 < n", auto)
  next
    show "v ` UNIV = UNIV - {n}"
    proof(auto simp add: v_def)
      fix m assume *: "m \<noteq> n" and **: "m \<notin> Suc ` {m'. \<not> m' < n}"
      {assume "n \<le> m" with * have 71: "Suc n \<le> m" by auto
       then obtain m' where 72: "m = Suc m'" using Suc_le_D by auto
       with 71 have "n \<le> m'" by auto
       with 72 ** have False by auto
      }
      thus "m < n" by force
    qed
  qed
  (*  *)
  obtain h' where h'_def: "h' = g o v o (inv g)" by blast
  hence 8: "bij_betw h' A' (A' - {a})" using 5 7 6
  by (auto simp add: bij_betw_trans)
  (*  *)
  obtain h where h_def: "h = (\<lambda> b. if b \<in> A' then h' b else b)" by blast
  have "\<forall>b \<in> A'. h b = h' b" unfolding h_def by auto
  hence "bij_betw h  A' (A' - {a})" using 8 bij_betw_cong[of A' h] by auto
  moreover
  {have "\<forall>b \<in> A - A'. h b = b" unfolding h_def by auto
   hence "bij_betw h  (A - A') (A - A')"
   using bij_betw_cong[of "A - A'" h id] bij_betw_id[of "A - A'"] by auto
  }
  moreover
  have "(A' Int (A - A') = {} \<and> A' \<union> (A - A') = A) \<and>
        ((A' - {a}) Int (A - A') = {} \<and> (A' - {a}) \<union> (A - A') = A - {a})"
  using 4 by blast
  ultimately have "bij_betw h A (A - {a})"
  using bij_betw_combine[of h A' "A' - {a}" "A - A'" "A - A'"] by simp
  thus ?thesis by blast
qed


lemma infinite_imp_bij_betw2:
assumes INF: "\<not> finite A"
shows "\<exists>h. bij_betw h A (A \<union> {a})"
proof(cases "a \<in> A")
  assume Case1: "a \<in> A"  hence "A \<union> {a} = A" by blast
  thus ?thesis using bij_betw_id[of A] by auto
next
  let ?A' = "A \<union> {a}"
  assume Case2: "a \<notin> A" hence "A = ?A' - {a}" by blast
  moreover have "\<not> finite ?A'" using INF by auto
  ultimately obtain f where "bij_betw f ?A' A"
  using infinite_imp_bij_betw[of ?A' a] by auto
  hence "bij_betw(inv_into ?A' f) A ?A'" using bij_betw_inv_into by blast
  thus ?thesis by auto
qed


subsection {* Properties involving Hilbert choice *}


lemma bij_betw_inv_into_left:
assumes BIJ: "bij_betw f A A'" and IN: "a \<in> A"
shows "(inv_into A f) (f a) = a"
using assms unfolding bij_betw_def
by clarify (rule inv_into_f_f)

lemma bij_betw_inv_into_right:
assumes "bij_betw f A A'" "a' \<in> A'"
shows "f(inv_into A f a') = a'"
using assms unfolding bij_betw_def using f_inv_into_f by force


lemma bij_betw_inv_into_subset:
assumes BIJ: "bij_betw f A A'" and
        SUB: "B \<le> A" and IM: "f ` B = B'"
shows "bij_betw (inv_into A f) B' B"
using assms unfolding bij_betw_def
by (auto intro: inj_on_inv_into)



end
