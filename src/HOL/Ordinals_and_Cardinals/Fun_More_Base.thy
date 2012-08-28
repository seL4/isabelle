(*  Title:      HOL/Ordinals_and_Cardinals/Fun_More_Base.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

More on injections, bijections and inverses (base).
*)

header {* More on Injections, Bijections and Inverses (Base) *}

theory Fun_More_Base
imports "~~/src/HOL/Library/Infinite_Set"
begin


text {* This section proves more facts (additional to those in @{text "Fun.thy"},
@{text "Hilbert_Choice.thy"}, @{text "Finite_Set.thy"} and @{text "Infinite_Set.thy"}),
mainly concerning injections, bijections, inverses and (numeric) cardinals of
finite sets. *}


subsection {* Purely functional properties  *}


(*2*)lemma bij_betw_id_iff:
"(A = B) = (bij_betw id A B)"
by(simp add: bij_betw_def)


(*2*)lemma bij_betw_byWitness:
assumes LEFT: "\<forall>a \<in> A. f'(f a) = a" and
        RIGHT: "\<forall>a' \<in> A'. f(f' a') = a'" and
        IM1: "f ` A \<le> A'" and IM2: "f' ` A' \<le> A"
shows "bij_betw f A A'"
using assms
proof(unfold bij_betw_def inj_on_def, auto)
  fix a b assume *: "a \<in> A" "b \<in> A" and **: "f a = f b"
  have "a = f'(f a) \<and> b = f'(f b)" using * LEFT by simp
  with ** show "a = b" by simp
next
  fix a' assume *: "a' \<in> A'"
  hence "f' a' \<in> A" using IM2 by blast
  moreover
  have "a' = f(f' a')" using * RIGHT by simp
  ultimately show "a' \<in> f ` A" by blast
qed


(*3*)corollary notIn_Un_bij_betw:
assumes NIN: "b \<notin> A" and NIN': "f b \<notin> A'" and
       BIJ: "bij_betw f A A'"
shows "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
proof-
  have "bij_betw f {b} {f b}"
  unfolding bij_betw_def inj_on_def by simp
  with assms show ?thesis
  using bij_betw_combine[of f A A' "{b}" "{f b}"] by blast
qed


(*1*)lemma notIn_Un_bij_betw3:
assumes NIN: "b \<notin> A" and NIN': "f b \<notin> A'"
shows "bij_betw f A A' = bij_betw f (A \<union> {b}) (A' \<union> {f b})"
proof
  assume "bij_betw f A A'"
  thus "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
  using assms notIn_Un_bij_betw[of b A f A'] by blast
next
  assume *: "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
  have "f ` A = A'"
  proof(auto)
    fix a assume **: "a \<in> A"
    hence "f a \<in> A' \<union> {f b}" using * unfolding bij_betw_def by blast
    moreover
    {assume "f a = f b"
     hence "a = b" using * ** unfolding bij_betw_def inj_on_def by blast
     with NIN ** have False by blast
    }
    ultimately show "f a \<in> A'" by blast
  next
    fix a' assume **: "a' \<in> A'"
    hence "a' \<in> f`(A \<union> {b})"
    using * by (auto simp add: bij_betw_def)
    then obtain a where 1: "a \<in> A \<union> {b} \<and> f a = a'" by blast
    moreover
    {assume "a = b" with 1 ** NIN' have False by blast
    }
    ultimately have "a \<in> A" by blast
    with 1 show "a' \<in> f ` A" by blast
  qed
  thus "bij_betw f A A'" using * bij_betw_subset[of f "A \<union> {b}" _ A] by blast
qed


subsection {* Properties involving finite and infinite sets *}


(*3*)lemma inj_on_finite:
assumes "inj_on f A" "f ` A \<le> B" "finite B"
shows "finite A"
using assms infinite_super by (fast dest: finite_imageD)


(*3*)lemma infinite_imp_bij_betw:
assumes INF: "infinite A"
shows "\<exists>h. bij_betw h A (A - {a})"
proof(cases "a \<in> A")
  assume Case1: "a \<notin> A"  hence "A - {a} = A" by blast
  thus ?thesis using bij_betw_id[of A] by auto
next
  assume Case2: "a \<in> A"
  have "infinite (A - {a})" using INF infinite_remove by auto
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


(*3*)lemma infinite_imp_bij_betw2:
assumes INF: "infinite A"
shows "\<exists>h. bij_betw h A (A \<union> {a})"
proof(cases "a \<in> A")
  assume Case1: "a \<in> A"  hence "A \<union> {a} = A" by blast
  thus ?thesis using bij_betw_id[of A] by auto
next
  let ?A' = "A \<union> {a}"
  assume Case2: "a \<notin> A" hence "A = ?A' - {a}" by blast
  moreover have "infinite ?A'" using INF by auto
  ultimately obtain f where "bij_betw f ?A' A"
  using infinite_imp_bij_betw[of ?A' a] by auto
  hence "bij_betw(inv_into ?A' f) A ?A'" using bij_betw_inv_into by blast
  thus ?thesis by auto
qed


subsection {* Properties involving Hilbert choice *}


(*2*)lemma bij_betw_inv_into_left:
assumes BIJ: "bij_betw f A A'" and IN: "a \<in> A"
shows "(inv_into A f) (f a) = a"
using assms unfolding bij_betw_def
by clarify (rule inv_into_f_f)

(*2*)lemma bij_betw_inv_into_right:
assumes "bij_betw f A A'" "a' \<in> A'"
shows "f(inv_into A f a') = a'"
using assms unfolding bij_betw_def using f_inv_into_f by force


(*1*)lemma bij_betw_inv_into_LEFT:
assumes BIJ: "bij_betw f A A'" and SUB: "B \<le> A"
shows "(inv_into A f)`(f ` B) = B"
using assms unfolding bij_betw_def using inv_into_image_cancel by force


(*1*)lemma bij_betw_inv_into_LEFT_RIGHT:
assumes BIJ: "bij_betw f A A'" and SUB: "B \<le> A" and
        IM: "f ` B = B'"
shows "(inv_into A f) ` B' = B"
using assms bij_betw_inv_into_LEFT[of f A A' B] by fast


(*1*)lemma bij_betw_inv_into_subset:
assumes BIJ: "bij_betw f A A'" and
        SUB: "B \<le> A" and IM: "f ` B = B'"
shows "bij_betw (inv_into A f) B' B"
using assms unfolding bij_betw_def
by (auto intro: inj_on_inv_into)


subsection {* Other facts  *}


(*2*)lemma atLeastLessThan_less_eq:
"({0..<m} \<le> {0..<n}) = ((m::nat) \<le> n)"
unfolding ivl_subset by arith


(*2*)lemma atLeastLessThan_less_eq2:
assumes "inj_on f {0..<(m::nat)} \<and> f ` {0..<m} \<le> {0..<n}"
shows "m \<le> n"
using assms
using finite_atLeastLessThan[of m] finite_atLeastLessThan[of n]
      card_atLeastLessThan[of m] card_atLeastLessThan[of n]
      card_inj_on_le[of f "{0 ..< m}" "{0 ..< n}"] by auto



end
