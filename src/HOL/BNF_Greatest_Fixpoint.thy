(*  Title:      HOL/BNF_Greatest_Fixpoint.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013, 2014

Greatest fixpoint (codatatype) operation on bounded natural functors.
*)

section \<open>Greatest Fixpoint (Codatatype) Operation on Bounded Natural Functors\<close>

theory BNF_Greatest_Fixpoint
imports BNF_Fixpoint_Base String
keywords
  "codatatype" :: thy_decl and
  "primcorecursive" :: thy_goal and
  "primcorec" :: thy_decl
begin

alias proj = Equiv_Relations.proj

lemma one_pointE: "\<lbrakk>\<And>x. s = x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma obj_sumE: "\<lbrakk>\<forall>x. s = Inl x \<longrightarrow> P; \<forall>x. s = Inr x \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases s) auto

lemma not_TrueE: "\<not> True \<Longrightarrow> P"
  by (erule notE, rule TrueI)

lemma neq_eq_eq_contradict: "\<lbrakk>t \<noteq> u; s = t; s = u\<rbrakk> \<Longrightarrow> P"
  by fast

lemma converse_Times: "(A \<times> B)\<inverse> = B \<times> A"
  by fast

lemma equiv_proj:
  assumes e: "equiv A R" and m: "z \<in> R"
  shows "(proj R \<circ> fst) z = (proj R \<circ> snd) z"
proof -
  from m have z: "(fst z, snd z) \<in> R" by auto
  with e have "\<And>x. (fst z, x) \<in> R \<Longrightarrow> (snd z, x) \<in> R" "\<And>x. (snd z, x) \<in> R \<Longrightarrow> (fst z, x) \<in> R"
    unfolding equiv_def sym_def trans_def by blast+
  then show ?thesis unfolding proj_def[abs_def] by auto
qed

(* Operators: *)
definition image2 where "image2 A f g = {(f a, g a) | a. a \<in> A}"

lemma Id_on_Gr: "Id_on A = Gr A id"
  unfolding Id_on_def Gr_def by auto

lemma image2_eqI: "\<lbrakk>b = f x; c = g x; x \<in> A\<rbrakk> \<Longrightarrow> (b, c) \<in> image2 A f g"
  unfolding image2_def by auto

lemma IdD: "(a, b) \<in> Id \<Longrightarrow> a = b"
  by auto

lemma image2_Gr: "image2 A f g = (Gr A f)\<inverse> O (Gr A g)"
  unfolding image2_def Gr_def by auto

lemma GrD1: "(x, fx) \<in> Gr A f \<Longrightarrow> x \<in> A"
  unfolding Gr_def by simp

lemma GrD2: "(x, fx) \<in> Gr A f \<Longrightarrow> f x = fx"
  unfolding Gr_def by simp

lemma Gr_incl: "Gr A f \<subseteq> A \<times> B \<longleftrightarrow> f ` A \<subseteq> B"
  unfolding Gr_def by auto

lemma subset_Collect_iff: "B \<subseteq> A \<Longrightarrow> (B \<subseteq> {x \<in> A. P x}) = (\<forall>x \<in> B. P x)"
  by blast

lemma subset_CollectI: "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> Q x \<Longrightarrow> P x) \<Longrightarrow> ({x \<in> B. Q x} \<subseteq> {x \<in> A. P x})"
  by blast

lemma in_rel_Collect_case_prod_eq: "in_rel (Collect (case_prod X)) = X"
  unfolding fun_eq_iff by auto

lemma Collect_case_prod_in_rel_leI: "X \<subseteq> Y \<Longrightarrow> X \<subseteq> Collect (case_prod (in_rel Y))"
  by auto

lemma Collect_case_prod_in_rel_leE: "X \<subseteq> Collect (case_prod (in_rel Y)) \<Longrightarrow> (X \<subseteq> Y \<Longrightarrow> R) \<Longrightarrow> R"
  by force

lemma conversep_in_rel: "(in_rel R)\<inverse>\<inverse> = in_rel (R\<inverse>)"
  unfolding fun_eq_iff by auto

lemma relcompp_in_rel: "in_rel R OO in_rel S = in_rel (R O S)"
  unfolding fun_eq_iff by auto

lemma in_rel_Gr: "in_rel (Gr A f) = Grp A f"
  unfolding Gr_def Grp_def fun_eq_iff by auto

definition relImage where
  "relImage R f \<equiv> {(f a1, f a2) | a1 a2. (a1,a2) \<in> R}"

definition relInvImage where
  "relInvImage A R f \<equiv> {(a1, a2) | a1 a2. a1 \<in> A \<and> a2 \<in> A \<and> (f a1, f a2) \<in> R}"

lemma relImage_Gr:
  "\<lbrakk>R \<subseteq> A \<times> A\<rbrakk> \<Longrightarrow> relImage R f = (Gr A f)\<inverse> O R O Gr A f"
  unfolding relImage_def Gr_def relcomp_def by auto

lemma relInvImage_Gr: "\<lbrakk>R \<subseteq> B \<times> B\<rbrakk> \<Longrightarrow> relInvImage A R f = Gr A f O R O (Gr A f)\<inverse>"
  unfolding Gr_def relcomp_def image_def relInvImage_def by auto

lemma relImage_mono:
  "R1 \<subseteq> R2 \<Longrightarrow> relImage R1 f \<subseteq> relImage R2 f"
  unfolding relImage_def by auto

lemma relInvImage_mono:
  "R1 \<subseteq> R2 \<Longrightarrow> relInvImage A R1 f \<subseteq> relInvImage A R2 f"
  unfolding relInvImage_def by auto

lemma relInvImage_Id_on:
  "(\<And>a1 a2. f a1 = f a2 \<longleftrightarrow> a1 = a2) \<Longrightarrow> relInvImage A (Id_on B) f \<subseteq> Id"
  unfolding relInvImage_def Id_on_def by auto

lemma relInvImage_UNIV_relImage:
  "R \<subseteq> relInvImage UNIV (relImage R f) f"
  unfolding relInvImage_def relImage_def by auto

lemma relImage_proj:
  assumes "equiv A R"
  shows "relImage R (proj R) \<subseteq> Id_on (A//R)"
  unfolding relImage_def Id_on_def
  using proj_iff[OF assms] equiv_class_eq_iff[OF assms]
  by (auto simp: proj_preserves)

lemma relImage_relInvImage:
  assumes "R \<subseteq> f ` A \<times> f ` A"
  shows "relImage (relInvImage A R f) f = R"
  using assms unfolding relImage_def relInvImage_def by fast

lemma subst_Pair: "P x y \<Longrightarrow> a = (x, y) \<Longrightarrow> P (fst a) (snd a)"
  by simp

lemma fst_diag_id: "(fst \<circ> (\<lambda>x. (x, x))) z = id z" by simp
lemma snd_diag_id: "(snd \<circ> (\<lambda>x. (x, x))) z = id z" by simp

lemma fst_diag_fst: "fst \<circ> ((\<lambda>x. (x, x)) \<circ> fst) = fst" by auto
lemma snd_diag_fst: "snd \<circ> ((\<lambda>x. (x, x)) \<circ> fst) = fst" by auto
lemma fst_diag_snd: "fst \<circ> ((\<lambda>x. (x, x)) \<circ> snd) = snd" by auto
lemma snd_diag_snd: "snd \<circ> ((\<lambda>x. (x, x)) \<circ> snd) = snd" by auto

definition Succ where "Succ Kl kl = {k . kl @ [k] \<in> Kl}"
definition Shift where "Shift Kl k = {kl. k # kl \<in> Kl}"
definition shift where "shift lab k = (\<lambda>kl. lab (k # kl))"

lemma empty_Shift: "\<lbrakk>[] \<in> Kl; k \<in> Succ Kl []\<rbrakk> \<Longrightarrow> [] \<in> Shift Kl k"
  unfolding Shift_def Succ_def by simp

lemma SuccD: "k \<in> Succ Kl kl \<Longrightarrow> kl @ [k] \<in> Kl"
  unfolding Succ_def by simp

lemmas SuccE = SuccD[elim_format]

lemma SuccI: "kl @ [k] \<in> Kl \<Longrightarrow> k \<in> Succ Kl kl"
  unfolding Succ_def by simp

lemma ShiftD: "kl \<in> Shift Kl k \<Longrightarrow> k # kl \<in> Kl"
  unfolding Shift_def by simp

lemma Succ_Shift: "Succ (Shift Kl k) kl = Succ Kl (k # kl)"
  unfolding Succ_def Shift_def by auto

lemma length_Cons: "length (x # xs) = Suc (length xs)"
  by simp

lemma length_append_singleton: "length (xs @ [x]) = Suc (length xs)"
  by simp

(*injection into the field of a cardinal*)
definition "toCard_pred A r f \<equiv> inj_on f A \<and> f ` A \<subseteq> Field r \<and> Card_order r"
definition "toCard A r \<equiv> SOME f. toCard_pred A r f"

lemma ex_toCard_pred:
  "\<lbrakk>|A| \<le>o r; Card_order r\<rbrakk> \<Longrightarrow> \<exists> f. toCard_pred A r f"
  unfolding toCard_pred_def
  using card_of_ordLeq[of A "Field r"]
    ordLeq_ordIso_trans[OF _ card_of_unique[of "Field r" r], of "|A|"]
  by blast

lemma toCard_pred_toCard:
  "\<lbrakk>|A| \<le>o r; Card_order r\<rbrakk> \<Longrightarrow> toCard_pred A r (toCard A r)"
  unfolding toCard_def using someI_ex[OF ex_toCard_pred] .

lemma toCard_inj: "\<lbrakk>|A| \<le>o r; Card_order r; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> toCard A r x = toCard A r y \<longleftrightarrow> x = y"
  using toCard_pred_toCard unfolding inj_on_def toCard_pred_def by blast

definition "fromCard A r k \<equiv> SOME b. b \<in> A \<and> toCard A r b = k"

lemma fromCard_toCard:
  "\<lbrakk>|A| \<le>o r; Card_order r; b \<in> A\<rbrakk> \<Longrightarrow> fromCard A r (toCard A r b) = b"
  unfolding fromCard_def by (rule some_equality) (auto simp add: toCard_inj)

lemma Inl_Field_csum: "a \<in> Field r \<Longrightarrow> Inl a \<in> Field (r +c s)"
  unfolding Field_card_of csum_def by auto

lemma Inr_Field_csum: "a \<in> Field s \<Longrightarrow> Inr a \<in> Field (r +c s)"
  unfolding Field_card_of csum_def by auto

lemma rec_nat_0_imp: "f = rec_nat f1 (\<lambda>n rec. f2 n rec) \<Longrightarrow> f 0 = f1"
  by auto

lemma rec_nat_Suc_imp: "f = rec_nat f1 (\<lambda>n rec. f2 n rec) \<Longrightarrow> f (Suc n) = f2 n (f n)"
  by auto

lemma rec_list_Nil_imp: "f = rec_list f1 (\<lambda>x xs rec. f2 x xs rec) \<Longrightarrow> f [] = f1"
  by auto

lemma rec_list_Cons_imp: "f = rec_list f1 (\<lambda>x xs rec. f2 x xs rec) \<Longrightarrow> f (x # xs) = f2 x xs (f xs)"
  by auto

lemma not_arg_cong_Inr: "x \<noteq> y \<Longrightarrow> Inr x \<noteq> Inr y"
  by simp

definition image2p where
  "image2p f g R = (\<lambda>x y. \<exists>x' y'. R x' y' \<and> f x' = x \<and> g y' = y)"

lemma image2pI: "R x y \<Longrightarrow> image2p f g R (f x) (g y)"
  unfolding image2p_def by blast

lemma image2pE: "\<lbrakk>image2p f g R fx gy; (\<And>x y. fx = f x \<Longrightarrow> gy = g y \<Longrightarrow> R x y \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  unfolding image2p_def by blast

lemma rel_fun_iff_geq_image2p: "rel_fun R S f g = (image2p f g R \<le> S)"
  unfolding rel_fun_def image2p_def by auto

lemma rel_fun_image2p: "rel_fun R (image2p f g R) f g"
  unfolding rel_fun_def image2p_def by auto


subsection \<open>Equivalence relations, quotients, and Hilbert's choice\<close>

lemma equiv_Eps_in:
"\<lbrakk>equiv A r; X \<in> A//r\<rbrakk> \<Longrightarrow> Eps (\<lambda>x. x \<in> X) \<in> X"
  apply (rule someI2_ex)
  using in_quotient_imp_non_empty by blast

lemma equiv_Eps_preserves:
  assumes ECH: "equiv A r" and X: "X \<in> A//r"
  shows "Eps (\<lambda>x. x \<in> X) \<in> A"
  apply (rule in_mono[rule_format])
   using assms apply (rule in_quotient_imp_subset)
  by (rule equiv_Eps_in) (rule assms)+

lemma proj_Eps:
  assumes "equiv A r" and "X \<in> A//r"
  shows "proj r (Eps (\<lambda>x. x \<in> X)) = X"
unfolding proj_def
proof auto
  fix x assume x: "x \<in> X"
  thus "(Eps (\<lambda>x. x \<in> X), x) \<in> r" using assms equiv_Eps_in in_quotient_imp_in_rel by fast
next
  fix x assume "(Eps (\<lambda>x. x \<in> X),x) \<in> r"
  thus "x \<in> X" using in_quotient_imp_closed[OF assms equiv_Eps_in[OF assms]] by fast
qed

definition univ where "univ f X == f (Eps (\<lambda>x. x \<in> X))"

lemma univ_commute:
assumes ECH: "equiv A r" and RES: "f respects r" and x: "x \<in> A"
shows "(univ f) (proj r x) = f x"
proof (unfold univ_def)
  have prj: "proj r x \<in> A//r" using x proj_preserves by fast
  hence "Eps (\<lambda>y. y \<in> proj r x) \<in> A" using ECH equiv_Eps_preserves by fast
  moreover have "proj r (Eps (\<lambda>y. y \<in> proj r x)) = proj r x" using ECH prj proj_Eps by fast
  ultimately have "(x, Eps (\<lambda>y. y \<in> proj r x)) \<in> r" using x ECH proj_iff by fast
  thus "f (Eps (\<lambda>y. y \<in> proj r x)) = f x" using RES unfolding congruent_def by fastforce
qed

lemma univ_preserves:
  assumes ECH: "equiv A r" and RES: "f respects r" and PRES: "\<forall>x \<in> A. f x \<in> B"
  shows "\<forall>X \<in> A//r. univ f X \<in> B"
proof
  fix X assume "X \<in> A//r"
  then obtain x where x: "x \<in> A" and X: "X = proj r x" using ECH proj_image[of r A] by blast
  hence "univ f X = f x" using ECH RES univ_commute by fastforce
  thus "univ f X \<in> B" using x PRES by simp
qed

ML_file \<open>Tools/BNF/bnf_gfp_util.ML\<close>
ML_file \<open>Tools/BNF/bnf_gfp_tactics.ML\<close>
ML_file \<open>Tools/BNF/bnf_gfp.ML\<close>
ML_file \<open>Tools/BNF/bnf_gfp_rec_sugar_tactics.ML\<close>
ML_file \<open>Tools/BNF/bnf_gfp_rec_sugar.ML\<close>

end
