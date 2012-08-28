(*  Title:      HOL/Ordinals_and_Cardinals/Fun_More.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

More on injections, bijections and inverses.
*)

header {* More on Injections, Bijections and Inverses *}

theory Fun_More
imports "../Ordinals_and_Cardinals_Base/Fun_More_Base"
begin


subsection {* Purely functional properties  *}

(* unused *)
(*1*)lemma notIn_Un_bij_betw2:
assumes NIN: "b \<notin> A" and NIN': "b' \<notin> A'" and
        BIJ: "bij_betw f A A'"
shows "bij_betw f (A \<union> {b}) (A' \<union> {b'}) = (f b = b')"
proof
  assume "f b = b'"
  thus "bij_betw f (A \<union> {b}) (A' \<union> {b'})"
  using assms notIn_Un_bij_betw[of b A f A'] by auto
next
  assume *: "bij_betw f (A \<union> {b}) (A' \<union> {b'})"
  hence "f b \<in> A' \<union> {b'}"
  unfolding bij_betw_def by auto
  moreover
  {assume "f b \<in> A'"
   then obtain b1 where 1: "b1 \<in> A" and 2: "f b1 = f b" using BIJ
   by (auto simp add: bij_betw_def)
   hence "b = b1" using *
   by (auto simp add: bij_betw_def inj_on_def)
   with 1 NIN have False by auto
  }
  ultimately show "f b = b'" by blast
qed

(* unused *)
(*1*)lemma bij_betw_ball:
assumes BIJ: "bij_betw f A B"
shows "(\<forall>b \<in> B. phi b) = (\<forall>a \<in> A. phi(f a))"
using assms unfolding bij_betw_def inj_on_def by blast

(* unused *)
(*1*)lemma bij_betw_diff_singl:
assumes BIJ: "bij_betw f A A'" and IN: "a \<in> A"
shows "bij_betw f (A - {a}) (A' - {f a})"
proof-
  let ?B = "A - {a}"   let ?B' = "A' - {f a}"
  have "f a \<in> A'" using IN BIJ unfolding bij_betw_def by blast
  hence "a \<notin> ?B \<and> f a \<notin> ?B' \<and> A = ?B \<union> {a} \<and> A' = ?B' \<union> {f a}"
  using IN by blast
  thus ?thesis using notIn_Un_bij_betw3[of a ?B f ?B'] BIJ by simp
qed


subsection {* Properties involving finite and infinite sets *}

(*3*)lemma inj_on_image_Pow:
assumes "inj_on f A"
shows "inj_on (image f) (Pow A)"
unfolding Pow_def inj_on_def proof(clarsimp)
  fix X Y assume *: "X \<le> A" and **: "Y \<le> A" and
                 ***: "f ` X = f ` Y"
  show "X = Y"
  proof(auto)
    fix x assume ****: "x \<in> X"
    with *** obtain y where "y \<in> Y \<and> f x = f y" by blast
    with **** * ** assms show "x \<in> Y"
    unfolding inj_on_def by auto
  next
    fix y assume ****: "y \<in> Y"
    with *** obtain x where "x \<in> X \<and> f x = f y" by force
    with **** * ** assms show "y \<in> X"
    unfolding inj_on_def by auto
  qed
qed

(*2*)lemma bij_betw_image_Pow:
assumes "bij_betw f A B"
shows "bij_betw (image f) (Pow A) (Pow B)"
using assms unfolding bij_betw_def
by (auto simp add: inj_on_image_Pow image_Pow_surj)

(* unused *)
(*1*)lemma bij_betw_inv_into_RIGHT:
assumes BIJ: "bij_betw f A A'" and SUB: "B' \<le> A'"
shows "f `((inv_into A f)`B') = B'"
using assms
proof(auto simp add: bij_betw_inv_into_right)
  let ?f' = "(inv_into A f)"
  fix a' assume *: "a' \<in> B'"
  hence "a' \<in> A'" using SUB by auto
  hence "a' = f (?f' a')"
  using BIJ by (auto simp add: bij_betw_inv_into_right)
  thus "a' \<in> f ` (?f' ` B')" using * by blast
qed

(* unused *)
(*1*)lemma bij_betw_inv_into_RIGHT_LEFT:
assumes BIJ: "bij_betw f A A'" and SUB: "B' \<le> A'" and
        IM: "(inv_into A f) ` B' = B"
shows "f ` B = B'"
proof-
  have "f`((inv_into A f)` B') = B'"
  using assms bij_betw_inv_into_RIGHT[of f A A' B'] by auto
  thus ?thesis using IM by auto
qed

(* unused *)
(*2*)lemma bij_betw_inv_into_twice:
assumes "bij_betw f A A'"
shows "\<forall>a \<in> A. inv_into A' (inv_into A f) a = f a"
proof
  let ?f' = "inv_into A f"   let ?f'' = "inv_into A' ?f'"
  have 1: "bij_betw ?f' A' A" using assms
  by (auto simp add: bij_betw_inv_into)
  fix a assume *: "a \<in> A"
  then obtain a' where 2: "a' \<in> A'" and 3: "?f' a' = a"
  using 1 unfolding bij_betw_def by force
  hence "?f'' a = a'"
  using * 1 3 by (auto simp add: bij_betw_inv_into_left)
  moreover have "f a = a'" using assms 2 3
  by (auto simp add: bij_betw_inv_into_right)
  ultimately show "?f'' a = f a" by simp
qed


subsection {* Properties involving Hilbert choice *}


subsection {* Other facts *}

(*3*)lemma atLeastLessThan_injective:
assumes "{0 ..< m::nat} = {0 ..< n}"
shows "m = n"
proof-
  {assume "m < n"
   hence "m \<in> {0 ..< n}" by auto
   hence "{0 ..< m} < {0 ..< n}" by auto
   hence False using assms by blast
  }
  moreover
  {assume "n < m"
   hence "n \<in> {0 ..< m}" by auto
   hence "{0 ..< n} < {0 ..< m}" by auto
   hence False using assms by blast
  }
  ultimately show ?thesis by force
qed

(*2*)lemma atLeastLessThan_injective2:
"bij_betw f {0 ..< m::nat} {0 ..< n} \<Longrightarrow> m = n"
using finite_atLeastLessThan[of m] finite_atLeastLessThan[of n]
      card_atLeastLessThan[of m] card_atLeastLessThan[of n]
      bij_betw_iff_card[of "{0 ..< m}" "{0 ..< n}"] by auto

(* unused *)
(*2*)lemma atLeastLessThan_less_eq3:
"(\<exists>f. inj_on f {0..<(m::nat)} \<and> f ` {0..<m} \<le> {0..<n}) = (m \<le> n)"
using atLeastLessThan_less_eq2
proof(auto)
  assume "m \<le> n"
  hence "inj_on id {0..<m} \<and> id ` {0..<m} \<subseteq> {0..<n}" unfolding inj_on_def by force
  thus "\<exists>f. inj_on f {0..<m} \<and> f ` {0..<m} \<subseteq> {0..<n}" by blast
qed

(* unused *)
(*3*)lemma atLeastLessThan_less:
"({0..<m} < {0..<n}) = ((m::nat) < n)"
proof-
  have "({0..<m} < {0..<n}) = ({0..<m} \<le> {0..<n} \<and> {0..<m} ~= {0..<n})"
  using subset_iff_psubset_eq by blast
  also have "\<dots> = (m \<le> n \<and> m ~= n)"
  using atLeastLessThan_less_eq atLeastLessThan_injective by blast
  also have "\<dots> = (m < n)" by auto
  finally show ?thesis .
qed

end
