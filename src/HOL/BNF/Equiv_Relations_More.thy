(*  Title:      HOL/BNF/Equiv_Relations_More.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Some preliminaries on equivalence relations and quotients.
*)

header {* Some Preliminaries on Equivalence Relations and Quotients *}

theory Equiv_Relations_More
imports Equiv_Relations Hilbert_Choice
begin


(* Recall the following constants and lemmas:

term Eps
term "A//r"
lemmas equiv_def
lemmas refl_on_def
 -- note that "reflexivity on" also assumes inclusion of the relation's field into r

*)

definition proj where "proj r x = r `` {x}"

definition univ where "univ f X == f (Eps (%x. x \<in> X))"

lemma proj_preserves:
"x \<in> A \<Longrightarrow> proj r x \<in> A//r"
unfolding proj_def by (rule quotientI)

lemma proj_in_iff:
assumes "equiv A r"
shows "(proj r x \<in> A//r) = (x \<in> A)"
apply(rule iffI, auto simp add: proj_preserves)
unfolding proj_def quotient_def proof clarsimp
  fix y assume y: "y \<in> A" and "r `` {x} = r `` {y}"
  moreover have "y \<in> r `` {y}" using assms y unfolding equiv_def refl_on_def by blast
  ultimately have "(x,y) \<in> r" by blast
  thus "x \<in> A" using assms unfolding equiv_def refl_on_def by blast
qed

lemma proj_iff:
"\<lbrakk>equiv A r; {x,y} \<subseteq> A\<rbrakk> \<Longrightarrow> (proj r x = proj r y) = ((x,y) \<in> r)"
by (simp add: proj_def eq_equiv_class_iff)

(*
lemma in_proj: "\<lbrakk>equiv A r; x \<in> A\<rbrakk> \<Longrightarrow> x \<in> proj r x"
unfolding proj_def equiv_def refl_on_def by blast
*)

lemma proj_image: "(proj r) ` A = A//r"
unfolding proj_def[abs_def] quotient_def by blast

lemma in_quotient_imp_non_empty:
"\<lbrakk>equiv A r; X \<in> A//r\<rbrakk> \<Longrightarrow> X \<noteq> {}"
unfolding quotient_def using equiv_class_self by fast

lemma in_quotient_imp_in_rel:
"\<lbrakk>equiv A r; X \<in> A//r; {x,y} \<subseteq> X\<rbrakk> \<Longrightarrow> (x,y) \<in> r"
using quotient_eq_iff by fastforce

lemma in_quotient_imp_closed:
"\<lbrakk>equiv A r; X \<in> A//r; x \<in> X; (x,y) \<in> r\<rbrakk> \<Longrightarrow> y \<in> X"
unfolding quotient_def equiv_def trans_def by blast

lemma in_quotient_imp_subset:
"\<lbrakk>equiv A r; X \<in> A//r\<rbrakk> \<Longrightarrow> X \<subseteq> A"
using assms in_quotient_imp_in_rel equiv_type by fastforce

lemma equiv_Eps_in:
"\<lbrakk>equiv A r; X \<in> A//r\<rbrakk> \<Longrightarrow> Eps (%x. x \<in> X) \<in> X"
apply (rule someI2_ex)
using in_quotient_imp_non_empty by blast

lemma equiv_Eps_preserves:
assumes ECH: "equiv A r" and X: "X \<in> A//r"
shows "Eps (%x. x \<in> X) \<in> A"
apply (rule in_mono[rule_format])
 using assms apply (rule in_quotient_imp_subset)
by (rule equiv_Eps_in) (rule assms)+

lemma proj_Eps:
assumes "equiv A r" and "X \<in> A//r"
shows "proj r (Eps (%x. x \<in> X)) = X"
unfolding proj_def proof auto
  fix x assume x: "x \<in> X"
  thus "(Eps (%x. x \<in> X), x) \<in> r" using assms equiv_Eps_in in_quotient_imp_in_rel by fast
next
  fix x assume "(Eps (%x. x \<in> X),x) \<in> r"
  thus "x \<in> X" using in_quotient_imp_closed[OF assms equiv_Eps_in[OF assms]] by fast
qed

(*
lemma Eps_proj:
assumes "equiv A r" and "x \<in> A"
shows "(Eps (%y. y \<in> proj r x), x) \<in> r"
proof-
  have 1: "proj r x \<in> A//r" using assms proj_preserves by fastforce
  hence "Eps(%y. y \<in> proj r x) \<in> proj r x" using assms equiv_Eps_in by auto
  moreover have "x \<in> proj r x" using assms in_proj by fastforce
  ultimately show ?thesis using assms 1 in_quotient_imp_in_rel by fastforce
qed

lemma equiv_Eps_iff:
assumes "equiv A r" and "{X,Y} \<subseteq> A//r"
shows "((Eps (%x. x \<in> X),Eps (%y. y \<in> Y)) \<in> r) = (X = Y)"
proof-
  have "Eps (%x. x \<in> X) \<in> X \<and> Eps (%y. y \<in> Y) \<in> Y" using assms equiv_Eps_in by auto
  thus ?thesis using assms quotient_eq_iff by fastforce
qed

lemma equiv_Eps_inj_on:
assumes "equiv A r"
shows "inj_on (%X. Eps (%x. x \<in> X)) (A//r)"
unfolding inj_on_def proof clarify
  fix X Y assume X: "X \<in> A//r" and Y: "Y \<in> A//r" and Eps: "Eps (%x. x \<in> X) = Eps (%y. y \<in> Y)"
  hence "Eps (%x. x \<in> X) \<in> A" using assms equiv_Eps_preserves by auto
  hence "(Eps (%x. x \<in> X), Eps (%y. y \<in> Y)) \<in> r"
  using assms Eps unfolding quotient_def equiv_def refl_on_def by auto
  thus "X= Y" using X Y assms equiv_Eps_iff by auto
qed
*)

lemma univ_commute:
assumes ECH: "equiv A r" and RES: "f respects r" and x: "x \<in> A"
shows "(univ f) (proj r x) = f x"
unfolding univ_def proof -
  have prj: "proj r x \<in> A//r" using x proj_preserves by fast
  hence "Eps (%y. y \<in> proj r x) \<in> A" using ECH equiv_Eps_preserves by fast
  moreover have "proj r (Eps (%y. y \<in> proj r x)) = proj r x" using ECH prj proj_Eps by fast
  ultimately have "(x, Eps (%y. y \<in> proj r x)) \<in> r" using x ECH proj_iff by fast
  thus "f (Eps (%y. y \<in> proj r x)) = f x" using RES unfolding congruent_def by fastforce
qed

(*
lemma univ_unique:
assumes ECH: "equiv A r" and
        RES: "f respects r" and  COM: "\<forall> x \<in> A. G (proj r x) = f x"
shows "\<forall> X \<in> A//r. G X = univ f X"
proof
  fix X assume "X \<in> A//r"
  then obtain x where x: "x \<in> A" and X: "X = proj r x" using ECH proj_image[of r A] by blast
  have "G X = f x" unfolding X using x COM by simp
  thus "G X = univ f X" unfolding X using ECH RES x univ_commute by fastforce
qed
*)

lemma univ_preserves:
assumes ECH: "equiv A r" and RES: "f respects r" and
        PRES: "\<forall> x \<in> A. f x \<in> B"
shows "\<forall> X \<in> A//r. univ f X \<in> B"
proof
  fix X assume "X \<in> A//r"
  then obtain x where x: "x \<in> A" and X: "X = proj r x" using ECH proj_image[of r A] by blast
  hence "univ f X = f x" using assms univ_commute by fastforce
  thus "univ f X \<in> B" using x PRES by simp
qed

end
