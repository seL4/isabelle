(*  Title:      HOL/Cardinals/Fun_More.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

More on injections, bijections and inverses.
*)

section \<open>More on Injections, Bijections and Inverses\<close>

theory Fun_More
  imports Main
begin

subsection \<open>Purely functional properties\<close>

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


subsection \<open>Properties involving finite and infinite sets\<close>

(* unused *)
(*1*)lemma bij_betw_inv_into_RIGHT:
  assumes BIJ: "bij_betw f A A'" and SUB: "B' \<le> A'"
  shows "f `((inv_into A f)`B') = B'"
  by (metis BIJ SUB bij_betw_imp_surj_on image_inv_into_cancel)


(* unused *)
(*1*)lemma bij_betw_inv_into_RIGHT_LEFT:
  assumes BIJ: "bij_betw f A A'" and SUB: "B' \<le> A'" and
    IM: "(inv_into A f) ` B' = B"
  shows "f ` B = B'"
  by (metis BIJ IM SUB bij_betw_inv_into_RIGHT)

(* unused *)
(*2*)lemma bij_betw_inv_into_twice:
  assumes "bij_betw f A A'"
  shows "\<forall>a \<in> A. inv_into A' (inv_into A f) a = f a"
  by (simp add: assms inv_into_inv_into_eq)


subsection \<open>Properties involving Hilbert choice\<close>

(*1*)lemma bij_betw_inv_into_LEFT:
  assumes BIJ: "bij_betw f A A'" and SUB: "B \<le> A"
  shows "(inv_into A f)`(f ` B) = B"
  using assms unfolding bij_betw_def using inv_into_image_cancel by force

(*1*)lemma bij_betw_inv_into_LEFT_RIGHT:
  assumes BIJ: "bij_betw f A A'" and SUB: "B \<le> A" and
    IM: "f ` B = B'"
  shows "(inv_into A f) ` B' = B"
  using assms bij_betw_inv_into_LEFT[of f A A' B] by fast


subsection \<open>Other facts\<close>

(*3*)lemma atLeastLessThan_injective:
  assumes "{0 ..< m::nat} = {0 ..< n}"
  shows "m = n"
  using assms atLeast0LessThan by force

(*2*)lemma atLeastLessThan_injective2:
  "bij_betw f {0 ..< m::nat} {0 ..< n} \<Longrightarrow> m = n"
  using bij_betw_same_card by fastforce

(*2*)lemma atLeastLessThan_less_eq:
  "({0..<m} \<le> {0..<n}) = ((m::nat) \<le> n)"
  by auto

(*2*)lemma atLeastLessThan_less_eq2:
  assumes "inj_on f {0..<(m::nat)}" "f ` {0..<m} \<le> {0..<n}"
  shows "m \<le> n"
  by (metis assms card_inj_on_le card_lessThan finite_lessThan lessThan_atLeast0)

(* unused *)
(*3*)lemma atLeastLessThan_less:
  "({0..<m} < {0..<n}) = ((m::nat) < n)"
  by auto

end
