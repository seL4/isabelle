(*  Title:      HOL/BNF/BNF_GFP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Greatest fixed point operation on bounded natural functors.
*)

header {* Greatest Fixed Point Operation on Bounded Natural Functors *}

theory BNF_GFP
imports BNF_FP_Basic Equiv_Relations_More "~~/src/HOL/Library/Sublist"
keywords
  "codatatype" :: thy_decl and
  "primcorec" :: thy_goal and
  "sequential"
begin

lemma sum_case_expand_Inr: "f o Inl = g \<Longrightarrow> f x = sum_case g (f o Inr) x"
by (auto split: sum.splits)

lemma sum_case_expand_Inr': "f o Inl = g \<Longrightarrow> h = f o Inr \<longleftrightarrow> sum_case g h = f"
by (metis sum_case_o_inj(1,2) surjective_sum)

lemma converse_Times: "(A \<times> B) ^-1 = B \<times> A"
by auto

lemma equiv_triv1:
assumes "equiv A R" and "(a, b) \<in> R" and "(a, c) \<in> R"
shows "(b, c) \<in> R"
using assms unfolding equiv_def sym_def trans_def by blast

lemma equiv_triv2:
assumes "equiv A R" and "(a, b) \<in> R" and "(b, c) \<in> R"
shows "(a, c) \<in> R"
using assms unfolding equiv_def trans_def by blast

lemma equiv_proj:
  assumes e: "equiv A R" and "z \<in> R"
  shows "(proj R o fst) z = (proj R o snd) z"
proof -
  from assms(2) have z: "(fst z, snd z) \<in> R" by auto
  have P: "\<And>x. (fst z, x) \<in> R \<Longrightarrow> (snd z, x) \<in> R" by (erule equiv_triv1[OF e z])
  have "\<And>x. (snd z, x) \<in> R \<Longrightarrow> (fst z, x) \<in> R" by (erule equiv_triv2[OF e z])
  with P show ?thesis unfolding proj_def[abs_def] by auto
qed

(* Operators: *)
definition image2 where "image2 A f g = {(f a, g a) | a. a \<in> A}"


lemma Id_onD: "(a, b) \<in> Id_on A \<Longrightarrow> a = b"
unfolding Id_on_def by simp

lemma Id_onD': "x \<in> Id_on A \<Longrightarrow> fst x = snd x"
unfolding Id_on_def by auto

lemma Id_on_fst: "x \<in> Id_on A \<Longrightarrow> fst x \<in> A"
unfolding Id_on_def by auto

lemma Id_on_UNIV: "Id_on UNIV = Id"
unfolding Id_on_def by auto

lemma Id_on_Comp: "Id_on A = Id_on A O Id_on A"
unfolding Id_on_def by auto

lemma Id_on_Gr: "Id_on A = Gr A id"
unfolding Id_on_def Gr_def by auto

lemma Id_on_UNIV_I: "x = y \<Longrightarrow> (x, y) \<in> Id_on UNIV"
unfolding Id_on_def by auto

lemma image2_eqI: "\<lbrakk>b = f x; c = g x; x \<in> A\<rbrakk> \<Longrightarrow> (b, c) \<in> image2 A f g"
unfolding image2_def by auto

lemma IdD: "(a, b) \<in> Id \<Longrightarrow> a = b"
by auto

lemma image2_Gr: "image2 A f g = (Gr A f)^-1 O (Gr A g)"
unfolding image2_def Gr_def by auto

lemma GrD1: "(x, fx) \<in> Gr A f \<Longrightarrow> x \<in> A"
unfolding Gr_def by simp

lemma GrD2: "(x, fx) \<in> Gr A f \<Longrightarrow> f x = fx"
unfolding Gr_def by simp

lemma Gr_incl: "Gr A f \<subseteq> A <*> B \<longleftrightarrow> f ` A \<subseteq> B"
unfolding Gr_def by auto

lemma in_rel_Collect_split_eq: "in_rel (Collect (split X)) = X"
unfolding fun_eq_iff by auto

lemma Collect_split_in_rel_leI: "X \<subseteq> Y \<Longrightarrow> X \<subseteq> Collect (split (in_rel Y))"
by auto

lemma Collect_split_in_rel_leE: "X \<subseteq> Collect (split (in_rel Y)) \<Longrightarrow> (X \<subseteq> Y \<Longrightarrow> R) \<Longrightarrow> R"
by force

lemma Collect_split_in_relI: "x \<in> X \<Longrightarrow> x \<in> Collect (split (in_rel X))"
by auto

lemma conversep_in_rel: "(in_rel R)\<inverse>\<inverse> = in_rel (R\<inverse>)"
unfolding fun_eq_iff by auto

lemma relcompp_in_rel: "in_rel R OO in_rel S = in_rel (R O S)"
unfolding fun_eq_iff by auto

lemma in_rel_Gr: "in_rel (Gr A f) = Grp A f"
unfolding Gr_def Grp_def fun_eq_iff by auto

lemma in_rel_Id_on_UNIV: "in_rel (Id_on UNIV) = op ="
unfolding fun_eq_iff by auto

definition relImage where
"relImage R f \<equiv> {(f a1, f a2) | a1 a2. (a1,a2) \<in> R}"

definition relInvImage where
"relInvImage A R f \<equiv> {(a1, a2) | a1 a2. a1 \<in> A \<and> a2 \<in> A \<and> (f a1, f a2) \<in> R}"

lemma relImage_Gr:
"\<lbrakk>R \<subseteq> A \<times> A\<rbrakk> \<Longrightarrow> relImage R f = (Gr A f)^-1 O R O Gr A f"
unfolding relImage_def Gr_def relcomp_def by auto

lemma relInvImage_Gr: "\<lbrakk>R \<subseteq> B \<times> B\<rbrakk> \<Longrightarrow> relInvImage A R f = Gr A f O R O (Gr A f)^-1"
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

lemma equiv_Image: "equiv A R \<Longrightarrow> (\<And>a b. (a, b) \<in> R \<Longrightarrow> a \<in> A \<and> b \<in> A \<and> R `` {a} = R `` {b})"
unfolding equiv_def refl_on_def Image_def by (auto intro: transD symD)

lemma relImage_proj:
assumes "equiv A R"
shows "relImage R (proj R) \<subseteq> Id_on (A//R)"
unfolding relImage_def Id_on_def
using proj_iff[OF assms] equiv_class_eq_iff[OF assms]
by (auto simp: proj_preserves)

lemma relImage_relInvImage:
assumes "R \<subseteq> f ` A <*> f ` A"
shows "relImage (relInvImage A R f) f = R"
using assms unfolding relImage_def relInvImage_def by fastforce

lemma subst_Pair: "P x y \<Longrightarrow> a = (x, y) \<Longrightarrow> P (fst a) (snd a)"
by simp

lemma fst_diag_id: "(fst \<circ> (%x. (x, x))) z = id z"
by simp

lemma snd_diag_id: "(snd \<circ> (%x. (x, x))) z = id z"
by simp

lemma image_convolD: "\<lbrakk>(a, b) \<in> <f, g> ` X\<rbrakk> \<Longrightarrow> \<exists>x. x \<in> X \<and> a = f x \<and> b = g x"
unfolding convol_def by auto

(*Extended Sublist*)

definition prefCl where
  "prefCl Kl = (\<forall> kl1 kl2. prefixeq kl1 kl2 \<and> kl2 \<in> Kl \<longrightarrow> kl1 \<in> Kl)"
definition PrefCl where
  "PrefCl A n = (\<forall>kl kl'. kl \<in> A n \<and> prefixeq kl' kl \<longrightarrow> (\<exists>m\<le>n. kl' \<in> A m))"

lemma prefCl_UN:
  "\<lbrakk>\<And>n. PrefCl A n\<rbrakk> \<Longrightarrow> prefCl (\<Union>n. A n)"
unfolding prefCl_def PrefCl_def by fastforce

definition Succ where "Succ Kl kl = {k . kl @ [k] \<in> Kl}"
definition Shift where "Shift Kl k = {kl. k # kl \<in> Kl}"
definition shift where "shift lab k = (\<lambda>kl. lab (k # kl))"

lemma empty_Shift: "\<lbrakk>[] \<in> Kl; k \<in> Succ Kl []\<rbrakk> \<Longrightarrow> [] \<in> Shift Kl k"
unfolding Shift_def Succ_def by simp

lemma Shift_clists: "Kl \<subseteq> Field (clists r) \<Longrightarrow> Shift Kl k \<subseteq> Field (clists r)"
unfolding Shift_def clists_def Field_card_of by auto

lemma Shift_prefCl: "prefCl Kl \<Longrightarrow> prefCl (Shift Kl k)"
unfolding prefCl_def Shift_def
proof safe
  fix kl1 kl2
  assume "\<forall>kl1 kl2. prefixeq kl1 kl2 \<and> kl2 \<in> Kl \<longrightarrow> kl1 \<in> Kl"
    "prefixeq kl1 kl2" "k # kl2 \<in> Kl"
  thus "k # kl1 \<in> Kl" using Cons_prefixeq_Cons[of k kl1 k kl2] by blast
qed

lemma not_in_Shift: "kl \<notin> Shift Kl x \<Longrightarrow> x # kl \<notin> Kl"
unfolding Shift_def by simp

lemma SuccD: "k \<in> Succ Kl kl \<Longrightarrow> kl @ [k] \<in> Kl"
unfolding Succ_def by simp

lemmas SuccE = SuccD[elim_format]

lemma SuccI: "kl @ [k] \<in> Kl \<Longrightarrow> k \<in> Succ Kl kl"
unfolding Succ_def by simp

lemma ShiftD: "kl \<in> Shift Kl k \<Longrightarrow> k # kl \<in> Kl"
unfolding Shift_def by simp

lemma Succ_Shift: "Succ (Shift Kl k) kl = Succ Kl (k # kl)"
unfolding Succ_def Shift_def by auto

lemma Nil_clists: "{[]} \<subseteq> Field (clists r)"
unfolding clists_def Field_card_of by auto

lemma Cons_clists:
  "\<lbrakk>x \<in> Field r; xs \<in> Field (clists r)\<rbrakk> \<Longrightarrow> x # xs \<in> Field (clists r)"
unfolding clists_def Field_card_of by auto

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

lemma toCard_inj: "\<lbrakk>|A| \<le>o r; Card_order r; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow>
  toCard A r x = toCard A r y \<longleftrightarrow> x = y"
using toCard_pred_toCard unfolding inj_on_def toCard_pred_def by blast

lemma toCard: "\<lbrakk>|A| \<le>o r; Card_order r; b \<in> A\<rbrakk> \<Longrightarrow> toCard A r b \<in> Field r"
using toCard_pred_toCard unfolding toCard_pred_def by blast

definition "fromCard A r k \<equiv> SOME b. b \<in> A \<and> toCard A r b = k"

lemma fromCard_toCard:
"\<lbrakk>|A| \<le>o r; Card_order r; b \<in> A\<rbrakk> \<Longrightarrow> fromCard A r (toCard A r b) = b"
unfolding fromCard_def by (rule some_equality) (auto simp add: toCard_inj)

(* pick according to the weak pullback *)
definition pickWP where
"pickWP A p1 p2 b1 b2 \<equiv> SOME a. a \<in> A \<and> p1 a = b1 \<and> p2 a = b2"

lemma pickWP_pred:
assumes "wpull A B1 B2 f1 f2 p1 p2" and
"b1 \<in> B1" and "b2 \<in> B2" and "f1 b1 = f2 b2"
shows "\<exists> a. a \<in> A \<and> p1 a = b1 \<and> p2 a = b2"
using assms unfolding wpull_def by blast

lemma pickWP:
assumes "wpull A B1 B2 f1 f2 p1 p2" and
"b1 \<in> B1" and "b2 \<in> B2" and "f1 b1 = f2 b2"
shows "pickWP A p1 p2 b1 b2 \<in> A"
      "p1 (pickWP A p1 p2 b1 b2) = b1"
      "p2 (pickWP A p1 p2 b1 b2) = b2"
unfolding pickWP_def using assms someI_ex[OF pickWP_pred] by fastforce+

lemma Inl_Field_csum: "a \<in> Field r \<Longrightarrow> Inl a \<in> Field (r +c s)"
unfolding Field_card_of csum_def by auto

lemma Inr_Field_csum: "a \<in> Field s \<Longrightarrow> Inr a \<in> Field (r +c s)"
unfolding Field_card_of csum_def by auto

lemma nat_rec_0: "f = nat_rec f1 (%n rec. f2 n rec) \<Longrightarrow> f 0 = f1"
by auto

lemma nat_rec_Suc: "f = nat_rec f1 (%n rec. f2 n rec) \<Longrightarrow> f (Suc n) = f2 n (f n)"
by auto

lemma list_rec_Nil: "f = list_rec f1 (%x xs rec. f2 x xs rec) \<Longrightarrow> f [] = f1"
by auto

lemma list_rec_Cons: "f = list_rec f1 (%x xs rec. f2 x xs rec) \<Longrightarrow> f (x # xs) = f2 x xs (f xs)"
by auto

lemma not_arg_cong_Inr: "x \<noteq> y \<Longrightarrow> Inr x \<noteq> Inr y"
by simp

lemma Collect_splitD: "x \<in> Collect (split A) \<Longrightarrow> A (fst x) (snd x)"
by auto

definition image2p where
  "image2p f g R = (\<lambda>x y. \<exists>x' y'. R x' y' \<and> f x' = x \<and> g y' = y)"

lemma image2pI: "R x y \<Longrightarrow> (image2p f g R) (f x) (g y)"
  unfolding image2p_def by blast

lemma image2p_eqI: "\<lbrakk>fx = f x; gy = g y; R x y\<rbrakk> \<Longrightarrow> (image2p f g R) fx gy"
  unfolding image2p_def by blast

lemma image2pE: "\<lbrakk>(image2p f g R) fx gy; (\<And>x y. fx = f x \<Longrightarrow> gy = g y \<Longrightarrow> R x y \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  unfolding image2p_def by blast

lemma fun_rel_iff_geq_image2p: "(fun_rel R S) f g = (image2p f g R \<le> S)"
  unfolding fun_rel_def image2p_def by auto

lemma convol_image_image2p: "<f o fst, g o snd> ` Collect (split R) \<subseteq> Collect (split (image2p f g R))"
  unfolding convol_def image2p_def by fastforce

lemma fun_rel_image2p: "(fun_rel R (image2p f g R)) f g"
  unfolding fun_rel_def image2p_def by auto

ML_file "Tools/bnf_gfp_util.ML"
ML_file "Tools/bnf_gfp_tactics.ML"
ML_file "Tools/bnf_gfp.ML"

end
