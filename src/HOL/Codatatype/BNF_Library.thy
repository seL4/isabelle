(*  Title:      HOL/Codatatype/BNF_Library.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Library for bounded natural functors.
*)

header {* Library for Bounded Natural Functors *}

theory BNF_Library
imports
   "../Ordinals_and_Cardinals_Base/Cardinal_Arithmetic"
   "~~/src/HOL/Library/List_Prefix"
   Equiv_Relations_More
begin

lemma subset_Collect_iff: "B \<subseteq> A \<Longrightarrow> (B \<subseteq> {x \<in> A. P x}) = (\<forall>x \<in> B. P x)"
by blast

lemma subset_CollectI: "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> Q x \<Longrightarrow> P x) \<Longrightarrow> ({x \<in> B. Q x} \<subseteq> {x \<in> A. P x})"
by blast

lemma mem_Collect_eq_split: "{(x, y). (x, y) \<in> X} = X"
by simp

lemma image_comp: "image (f o g) = image f o image g"
by (rule ext) (auto simp only: o_apply image_def)

lemma empty_natural: "(\<lambda>_. {}) o f = image g o (\<lambda>_. {})"
by (rule ext) simp

lemma Union_natural: "Union o image (image f) = image f o Union"
by (rule ext) (auto simp only: o_apply)

lemma in_Union_o_assoc: "x \<in> (Union o gset o gmap) A \<Longrightarrow> x \<in> (Union o (gset o gmap)) A"
by (unfold o_assoc)

lemma comp_single_set_bd:
  assumes fbd_Card_order: "Card_order fbd" and
    fset_bd: "\<And>x. |fset x| \<le>o fbd" and
    gset_bd: "\<And>x. |gset x| \<le>o gbd"
  shows "|\<Union>fset ` gset x| \<le>o gbd *c fbd"
apply (subst sym[OF SUP_def])
apply (rule ordLeq_transitive)
apply (rule card_of_UNION_Sigma)
apply (subst SIGMA_CSUM)
apply (rule ordLeq_transitive)
apply (rule card_of_Csum_Times')
apply (rule fbd_Card_order)
apply (rule ballI)
apply (rule fset_bd)
apply (rule ordLeq_transitive)
apply (rule cprod_mono1)
apply (rule gset_bd)
apply (rule ordIso_imp_ordLeq)
apply (rule ordIso_refl)
apply (rule Card_order_cprod)
done

lemma Union_image_insert: "\<Union>f ` insert a B = f a \<union> \<Union>f ` B"
by simp

lemma Union_image_empty: "A \<union> \<Union>f ` {} = A"
by simp

definition collect where
  "collect F x = (\<Union>f \<in> F. f x)"

lemma collect_o: "collect F o g = collect ((\<lambda>f. f o g) ` F)"
by (rule ext) (auto simp only: o_apply collect_def)

lemma image_o_collect: "collect ((\<lambda>f. image g o f) ` F) = image g o collect F"
by (rule ext) (auto simp add: collect_def)

lemma conj_subset_def: "A \<subseteq> {x. P x \<and> Q x} = (A \<subseteq> {x. P x} \<and> A \<subseteq> {x. Q x})"
by auto

lemma subset_emptyI: "(\<And>x. x \<in> A \<Longrightarrow> False) \<Longrightarrow> A \<subseteq> {}"
by auto

lemma rev_bspec: "a \<in> A \<Longrightarrow> \<forall>z \<in> A. P z \<Longrightarrow> P a"
by simp

lemma Un_cong: "\<lbrakk>A = B; C = D\<rbrakk> \<Longrightarrow> A \<union> C = B \<union> D"
by auto

lemma UN_image_subset: "\<Union>f ` g x \<subseteq> X = (g x \<subseteq> {x. f x \<subseteq> X})"
by auto

lemma image_Collect_subsetI:
  "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> f ` {x. P x} \<subseteq> B"
by auto

lemma comp_set_bd_Union_o_collect: "|\<Union>\<Union>(\<lambda>f. f x) ` X| \<le>o hbd \<Longrightarrow> |(Union \<circ> collect X) x| \<le>o hbd"
by (unfold o_apply collect_def SUP_def)

lemma sum_case_comp_Inl:
"sum_case f g \<circ> Inl = f"
unfolding comp_def by simp

lemma sum_case_expand_Inr: "f o Inl = g \<Longrightarrow> f x = sum_case g (f o Inr) x"
by (auto split: sum.splits)

lemma converse_mono:
"R1 ^-1 \<subseteq> R2 ^-1 \<longleftrightarrow> R1 \<subseteq> R2"
unfolding converse_def by auto

lemma converse_shift:
"R1 \<subseteq> R2 ^-1 \<Longrightarrow> R1 ^-1 \<subseteq> R2"
unfolding converse_def by auto

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


section{* Weak pullbacks: *}

definition csquare where
"csquare A f1 f2 p1 p2 \<longleftrightarrow> (\<forall> a \<in> A. f1 (p1 a) = f2 (p2 a))"

definition wpull where
"wpull A B1 B2 f1 f2 p1 p2 \<longleftrightarrow>
 (\<forall> b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<longrightarrow> (\<exists> a \<in> A. p1 a = b1 \<and> p2 a = b2))"

lemma wpull_cong:
"\<lbrakk>A' = A; B1' = B1; B2' = B2; wpull A B1 B2 f1 f2 p1 p2\<rbrakk> \<Longrightarrow> wpull A' B1' B2' f1 f2 p1 p2"
by simp

lemma wpull_id: "wpull UNIV B1 B2 id id id id"
unfolding wpull_def by simp


(* Weak pseudo-pullbacks *)

definition wppull where
"wppull A B1 B2 f1 f2 e1 e2 p1 p2 \<longleftrightarrow>
 (\<forall> b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<longrightarrow>
           (\<exists> a \<in> A. e1 (p1 a) = e1 b1 \<and> e2 (p2 a) = e2 b2))"


(* The pullback of sets *)
definition thePull where
"thePull B1 B2 f1 f2 = {(b1,b2). b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2}"

lemma wpull_thePull:
"wpull (thePull B1 B2 f1 f2) B1 B2 f1 f2 fst snd"
unfolding wpull_def thePull_def by auto

lemma wppull_thePull:
assumes "wppull A B1 B2 f1 f2 e1 e2 p1 p2"
shows
"\<exists> j. \<forall> a' \<in> thePull B1 B2 f1 f2.
   j a' \<in> A \<and>
   e1 (p1 (j a')) = e1 (fst a') \<and> e2 (p2 (j a')) = e2 (snd a')"
(is "\<exists> j. \<forall> a' \<in> ?A'. ?phi a' (j a')")
proof(rule bchoice[of ?A' ?phi], default)
  fix a' assume a': "a' \<in> ?A'"
  hence "fst a' \<in> B1" unfolding thePull_def by auto
  moreover
  from a' have "snd a' \<in> B2" unfolding thePull_def by auto
  moreover have "f1 (fst a') = f2 (snd a')"
  using a' unfolding csquare_def thePull_def by auto
  ultimately show "\<exists> ja'. ?phi a' ja'"
  using assms unfolding wppull_def by auto
qed

lemma wpull_wppull:
assumes wp: "wpull A' B1 B2 f1 f2 p1' p2'" and
1: "\<forall> a' \<in> A'. j a' \<in> A \<and> e1 (p1 (j a')) = e1 (p1' a') \<and> e2 (p2 (j a')) = e2 (p2' a')"
shows "wppull A B1 B2 f1 f2 e1 e2 p1 p2"
unfolding wppull_def proof safe
  fix b1 b2
  assume b1: "b1 \<in> B1" and b2: "b2 \<in> B2" and f: "f1 b1 = f2 b2"
  then obtain a' where a': "a' \<in> A'" and b1: "b1 = p1' a'" and b2: "b2 = p2' a'"
  using wp unfolding wpull_def by blast
  show "\<exists>a\<in>A. e1 (p1 a) = e1 b1 \<and> e2 (p2 a) = e2 b2"
  apply(rule bexI[of _ "j a'"]) unfolding b1 b2 using a' 1 by auto
qed

lemma wppull_id: "\<lbrakk>wpull UNIV UNIV UNIV f1 f2 p1 p2; e1 = id; e2 = id\<rbrakk> \<Longrightarrow>
   wppull UNIV UNIV UNIV f1 f2 e1 e2 p1 p2"
by (erule wpull_wppull) auto


(* Operators: *)
definition diag where "diag A \<equiv> {(a,a) | a. a \<in> A}"
definition "Gr A f = {(a,f a) | a. a \<in> A}"
definition image2 where "image2 A f g = {(f a, g a) | a. a \<in> A}"

lemma diagI: "x \<in> A \<Longrightarrow> (x, x) \<in> diag A"
unfolding diag_def by simp

lemma diagE: "(a, b) \<in> diag A \<Longrightarrow> a = b"
unfolding diag_def by simp

lemma diagE': "x \<in> diag A \<Longrightarrow> fst x = snd x"
unfolding diag_def by auto

lemma diag_fst: "x \<in> diag A \<Longrightarrow> fst x \<in> A"
unfolding diag_def by auto

lemma diag_UNIV: "diag UNIV = Id"
unfolding diag_def by auto

lemma diag_converse: "diag A = (diag A) ^-1"
unfolding diag_def by auto

lemma diag_Comp: "diag A = diag A O diag A"
unfolding diag_def by auto

lemma diag_Gr: "diag A = Gr A id"
unfolding diag_def Gr_def by simp

lemma diag_UNIV_I: "x = y \<Longrightarrow> (x, y) \<in> diag UNIV"
unfolding diag_def by auto

lemma image2_eqI: "\<lbrakk>b = f x; c = g x; x \<in> A\<rbrakk> \<Longrightarrow> (b, c) \<in> image2 A f g"
unfolding image2_def by auto

lemma Id_def': "Id = {(a,b). a = b}"
by auto

lemma Id_alt: "Id = Gr UNIV id"
unfolding Gr_def by auto

lemma Id_subset: "Id \<subseteq> {(a, b). P a b \<or> a = b}"
by auto

lemma IdD: "(a, b) \<in> Id \<Longrightarrow> a = b"
by auto

lemma image2_Gr: "image2 A f g = (Gr A f)^-1 O (Gr A g)"
unfolding image2_def Gr_def by auto

lemma GrI: "\<lbrakk>x \<in> A; f x = fx\<rbrakk> \<Longrightarrow> (x, fx) \<in> Gr A f"
unfolding Gr_def by simp

lemma GrE: "(x, fx) \<in> Gr A f \<Longrightarrow> (x \<in> A \<Longrightarrow> f x = fx \<Longrightarrow> P) \<Longrightarrow> P"
unfolding Gr_def by simp

lemma GrD1: "(x, fx) \<in> Gr A f \<Longrightarrow> x \<in> A"
unfolding Gr_def by simp

lemma GrD2: "(x, fx) \<in> Gr A f \<Longrightarrow> f x = fx"
unfolding Gr_def by simp

lemma Gr_UNIV_id: "f = id \<Longrightarrow> (Gr UNIV f)^-1 O Gr UNIV f = Gr UNIV f"
unfolding Gr_def by auto

lemma Gr_fst_snd: "(Gr R fst)^-1 O Gr R snd = R"
unfolding Gr_def by auto

lemma Gr_mono: "A \<subseteq> B \<Longrightarrow> Gr A f \<subseteq> Gr B f"
unfolding Gr_def by auto

lemma subst_rel_def: "A = B \<Longrightarrow> (Gr A f)^-1 O Gr A g = (Gr B f)^-1 O Gr B g"
by simp

lemma abs_pred_def: "\<lbrakk>\<And>x y. (x, y) \<in> rel = pred x y\<rbrakk> \<Longrightarrow> rel = Collect (split pred)"
by auto

lemma Collect_split_cong: "Collect (split pred) = Collect (split pred') \<Longrightarrow> pred = pred'"
by blast

lemma pred_def_abs: "rel = Collect (split pred) \<Longrightarrow> pred = (\<lambda>x y. (x, y) \<in> rel)"
by auto

lemma wpull_Gr:
"wpull (Gr A f) A (f ` A) f id fst snd"
unfolding wpull_def Gr_def by auto

lemma Gr_incl: "Gr A f \<subseteq> A <*> B \<longleftrightarrow> f ` A \<subseteq> B"
unfolding Gr_def by auto

lemma equiv_Image: "equiv A R \<Longrightarrow> (\<And>a b. (a, b) \<in> R \<Longrightarrow> a \<in> A \<and> b \<in> A \<and> R `` {a} = R `` {b})"
unfolding equiv_def refl_on_def Image_def by (auto intro: transD symD)

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

lemma relInvImage_diag:
"(\<And>a1 a2. f a1 = f a2 \<longleftrightarrow> a1 = a2) \<Longrightarrow> relInvImage A (diag B) f \<subseteq> Id"
unfolding relInvImage_def diag_def by auto

lemma relInvImage_UNIV_relImage:
"R \<subseteq> relInvImage UNIV (relImage R f) f"
unfolding relInvImage_def relImage_def by auto

lemma relImage_proj:
assumes "equiv A R"
shows "relImage R (proj R) \<subseteq> diag (A//R)"
unfolding relImage_def diag_def apply safe
using proj_iff[OF assms]
by (metis assms equiv_Image proj_def proj_preserves)

lemma relImage_relInvImage:
assumes "R \<subseteq> f ` A <*> f ` A"
shows "relImage (relInvImage A R f) f = R"
using assms unfolding relImage_def relInvImage_def by fastforce


(* Relation composition as a weak pseudo-pullback *)

(* pick middle *)
definition "pickM P Q a c = (SOME b. (a,b) \<in> P \<and> (b,c) \<in> Q)"

lemma pickM:
assumes "(a,c) \<in> P O Q"
shows "(a, pickM P Q a c) \<in> P \<and> (pickM P Q a c, c) \<in> Q"
unfolding pickM_def apply(rule someI_ex)
using assms unfolding relcomp_def by auto

definition fstO where "fstO P Q ac = (fst ac, pickM P Q (fst ac) (snd ac))"
definition sndO where "sndO P Q ac = (pickM P Q (fst ac) (snd ac), snd ac)"

lemma fstO_in: "ac \<in> P O Q \<Longrightarrow> fstO P Q ac \<in> P"
by (metis assms fstO_def pickM surjective_pairing)

lemma fst_fstO: "fst bc = (fst \<circ> fstO P Q) bc"
unfolding comp_def fstO_def by simp

lemma snd_sndO: "snd bc = (snd \<circ> sndO P Q) bc"
unfolding comp_def sndO_def by simp

lemma sndO_in: "ac \<in> P O Q \<Longrightarrow> sndO P Q ac \<in> Q"
by (metis assms sndO_def pickM surjective_pairing)

lemma csquare_fstO_sndO:
"csquare (P O Q) snd fst (fstO P Q) (sndO P Q)"
unfolding csquare_def fstO_def sndO_def using pickM by auto

lemma wppull_fstO_sndO:
shows "wppull (P O Q) P Q snd fst fst snd (fstO P Q) (sndO P Q)"
using pickM unfolding wppull_def fstO_def sndO_def relcomp_def by auto

lemma subst_Pair: "P x y \<Longrightarrow> a = (x, y) \<Longrightarrow> P (fst a) (snd a)"
by simp

lemma snd_fst_flip: "snd xy = (fst o (%(x, y). (y, x))) xy"
by (simp split: prod.split)

lemma fst_snd_flip: "fst xy = (snd o (%(x, y). (y, x))) xy"
by (simp split: prod.split)

lemma flip_rel: "A \<subseteq> (R ^-1) \<Longrightarrow> (%(x, y). (y, x)) ` A \<subseteq> R"
by auto

lemma fst_diag_id: "(fst \<circ> (%x. (x, x))) z = id z"
by simp

lemma snd_diag_id: "(snd \<circ> (%x. (x, x))) z = id z"
by simp

lemma fst_snd: "\<lbrakk>snd x = (y, z)\<rbrakk> \<Longrightarrow> fst (snd x) = y"
by simp

lemma snd_snd: "\<lbrakk>snd x = (y, z)\<rbrakk> \<Longrightarrow> snd (snd x) = z"
by simp

lemma fstI: "x = (y, z) \<Longrightarrow> fst x = y"
by simp

lemma sndI: "x = (y, z) \<Longrightarrow> snd x = z"
by simp

lemma Collect_restrict: "{x. x \<in> X \<and> P x} \<subseteq> X"
by auto

lemma Collect_restrict': "{(x, y) | x y. phi x y \<and> P x y} \<subseteq> {(x, y) | x y. phi x y}"
by auto

lemma prop_restrict: "\<lbrakk>x \<in> Z; Z \<subseteq> {x. x \<in> X \<and> P x}\<rbrakk> \<Longrightarrow> P x"
by auto

lemma underS_I: "\<lbrakk>i \<noteq> j; (i, j) \<in> R\<rbrakk> \<Longrightarrow> i \<in> rel.underS R j"
unfolding rel.underS_def by simp

lemma underS_E: "i \<in> rel.underS R j \<Longrightarrow> i \<noteq> j \<and> (i, j) \<in> R"
unfolding rel.underS_def by simp

lemma underS_Field: "i \<in> rel.underS R j \<Longrightarrow> i \<in> Field R"
unfolding rel.underS_def Field_def by auto

lemma FieldI2: "(i, j) \<in> R \<Longrightarrow> j \<in> Field R"
unfolding Field_def by auto


subsection {* Convolution product *}

definition convol ("<_ , _>") where
"<f , g> \<equiv> %a. (f a, g a)"

lemma fst_convol:
"fst o <f , g> = f"
apply(rule ext)
unfolding convol_def by simp

lemma snd_convol:
"snd o <f , g> = g"
apply(rule ext)
unfolding convol_def by simp

lemma fst_convol': "fst (<f, g> x) = f x"
using fst_convol unfolding convol_def by simp

lemma snd_convol': "snd (<f, g> x) = g x"
using snd_convol unfolding convol_def by simp

lemma image_convolD: "\<lbrakk>(a, b) \<in> <f, g> ` X\<rbrakk> \<Longrightarrow> \<exists>x. x \<in> X \<and> a = f x \<and> b = g x"
unfolding convol_def by auto

lemma convol_expand_snd: "fst o f = g \<Longrightarrow>  <g, snd o f> = f"
unfolding convol_def by auto

subsection{* Facts about functions *}

lemma pointfreeE: "f o g = f' o g' \<Longrightarrow> f (g x) = f' (g' x)"
unfolding o_def fun_eq_iff by simp

lemma pointfree_idE: "f o g = id \<Longrightarrow> f (g x) = x"
unfolding o_def fun_eq_iff by simp

definition inver where
  "inver g f A = (ALL a : A. g (f a) = a)"

lemma bij_betw_iff_ex:
  "bij_betw f A B = (EX g. g ` B = A \<and> inver g f A \<and> inver f g B)" (is "?L = ?R")
proof (rule iffI)
  assume ?L
  hence f: "f ` A = B" and inj_f: "inj_on f A" unfolding bij_betw_def by auto
  let ?phi = "% b a. a : A \<and> f a = b"
  have "ALL b : B. EX a. ?phi b a" using f by blast
  then obtain g where g: "ALL b : B. g b : A \<and> f (g b) = b"
    using bchoice[of B ?phi] by blast
  hence gg: "ALL b : f ` A. g b : A \<and> f (g b) = b" using f by blast
  have gf: "inver g f A" unfolding inver_def by (metis gg imageI inj_f the_inv_into_f_f)
  moreover have "g ` B \<le> A \<and> inver f g B" using g unfolding inver_def by blast
  moreover have "A \<le> g ` B"
  proof safe
    fix a assume a: "a : A"
    hence "f a : B" using f by auto
    moreover have "a = g (f a)" using a gf unfolding inver_def by auto
    ultimately show "a : g ` B" by blast
  qed
  ultimately show ?R by blast
next
  assume ?R
  then obtain g where g: "g ` B = A \<and> inver g f A \<and> inver f g B" by blast
  show ?L unfolding bij_betw_def
  proof safe
    show "inj_on f A" unfolding inj_on_def
    proof safe
      fix a1 a2 assume a: "a1 : A"  "a2 : A" and "f a1 = f a2"
      hence "g (f a1) = g (f a2)" by simp
      thus "a1 = a2" using a g unfolding inver_def by simp
    qed
  next
    fix a assume "a : A"
    then obtain b where b: "b : B" and a: "a = g b" using g by blast
    hence "b = f (g b)" using g unfolding inver_def by auto
    thus "f a : B" unfolding a using b by simp
  next
    fix b assume "b : B"
    hence "g b : A \<and> b = f (g b)" using g unfolding inver_def by auto
    thus "b : f ` A" by auto
  qed
qed

lemma bijI: "\<lbrakk>\<And>x y. (f x = f y) = (x = y); \<And>y. \<exists>x. y = f x\<rbrakk> \<Longrightarrow> bij f"
unfolding bij_def inj_on_def by auto blast

lemma bij_betw_ex_weakE:
  "\<lbrakk>bij_betw f A B\<rbrakk> \<Longrightarrow> \<exists>g. g ` B \<subseteq> A \<and> inver g f A \<and> inver f g B"
by (auto simp only: bij_betw_iff_ex)

lemma inver_surj: "\<lbrakk>g ` B \<subseteq> A; f ` A \<subseteq> B; inver g f A\<rbrakk> \<Longrightarrow> g ` B = A"
unfolding inver_def by auto (rule rev_image_eqI, auto)

lemma inver_mono: "\<lbrakk>A \<subseteq> B; inver f g B\<rbrakk> \<Longrightarrow> inver f g A"
unfolding inver_def by auto

lemma inver_pointfree: "inver f g A = (\<forall>a \<in> A. (f o g) a = a)"
unfolding inver_def by simp

lemma bij_betwE: "bij_betw f A B \<Longrightarrow> \<forall>a\<in>A. f a \<in> B"
unfolding bij_betw_def by auto

lemma bij_betw_imageE: "bij_betw f A B \<Longrightarrow> f ` A = B"
unfolding bij_betw_def by auto

lemma inverE: "\<lbrakk>inver f f' A; x \<in> A\<rbrakk> \<Longrightarrow> f (f' x) = x"
unfolding inver_def by auto

lemma bij_betw_inver1: "bij_betw f A B \<Longrightarrow> inver (inv_into A f) f A"
unfolding bij_betw_def inver_def by auto

lemma bij_betw_inver2: "bij_betw f A B \<Longrightarrow> inver f (inv_into A f) B"
unfolding bij_betw_def inver_def by auto

lemma bij_betwI: "\<lbrakk>bij_betw g B A; inver g f A; inver f g B\<rbrakk> \<Longrightarrow> bij_betw f A B"
by (metis bij_betw_iff_ex bij_betw_imageE)

lemma bij_betwI':
  "\<lbrakk>\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (f x = f y) = (x = y);
    \<And>x. x \<in> X \<Longrightarrow> f x \<in> Y;
    \<And>y. y \<in> Y \<Longrightarrow> \<exists>x \<in> X. y = f x\<rbrakk> \<Longrightarrow> bij_betw f X Y"
unfolding bij_betw_def inj_on_def by auto (metis rev_image_eqI)

lemma o_bij:
  assumes gf: "g o f = id" and fg: "f o g = id"
  shows "bij f"
unfolding bij_def inj_on_def surj_def proof safe
  fix a1 a2 assume "f a1 = f a2"
  hence "g ( f a1) = g (f a2)" by simp
  thus "a1 = a2" using gf unfolding fun_eq_iff by simp
next
  fix b
  have "b = f (g b)"
  using fg unfolding fun_eq_iff by simp
  thus "EX a. b = f a" by blast
qed

lemma surj_fun_eq:
  assumes surj_on: "f ` X = UNIV" and eq_on: "\<forall>x \<in> X. (g1 o f) x = (g2 o f) x"
  shows "g1 = g2"
proof (rule ext)
  fix y
  from surj_on obtain x where "x \<in> X" and "y = f x" by blast
  thus "g1 y = g2 y" using eq_on by simp
qed

lemma Card_order_wo_rel: "Card_order r \<Longrightarrow> wo_rel r"
unfolding wo_rel_def card_order_on_def by blast 

lemma Cinfinite_limit: "\<lbrakk>x \<in> Field r; Cinfinite r\<rbrakk> \<Longrightarrow>
  \<exists>y \<in> Field r. x \<noteq> y \<and> (x, y) \<in> r"
unfolding cinfinite_def by (auto simp add: infinite_Card_order_limit)

lemma Card_order_trans:
  "\<lbrakk>Card_order r; x \<noteq> y; (x, y) \<in> r; y \<noteq> z; (y, z) \<in> r\<rbrakk> \<Longrightarrow> x \<noteq> z \<and> (x, z) \<in> r"
unfolding card_order_on_def well_order_on_def linear_order_on_def
  partial_order_on_def preorder_on_def trans_def antisym_def by blast

lemma Cinfinite_limit2:
 assumes x1: "x1 \<in> Field r" and x2: "x2 \<in> Field r" and r: "Cinfinite r"
 shows "\<exists>y \<in> Field r. (x1 \<noteq> y \<and> (x1, y) \<in> r) \<and> (x2 \<noteq> y \<and> (x2, y) \<in> r)"
proof -
  from r have trans: "trans r" and total: "Total r" and antisym: "antisym r"
    unfolding card_order_on_def well_order_on_def linear_order_on_def
      partial_order_on_def preorder_on_def by auto
  obtain y1 where y1: "y1 \<in> Field r" "x1 \<noteq> y1" "(x1, y1) \<in> r"
    using Cinfinite_limit[OF x1 r] by blast
  obtain y2 where y2: "y2 \<in> Field r" "x2 \<noteq> y2" "(x2, y2) \<in> r"
    using Cinfinite_limit[OF x2 r] by blast
  show ?thesis
  proof (cases "y1 = y2")
    case True with y1 y2 show ?thesis by blast
  next
    case False
    with y1(1) y2(1) total have "(y1, y2) \<in> r \<or> (y2, y1) \<in> r"
      unfolding total_on_def by auto
    thus ?thesis
    proof
      assume *: "(y1, y2) \<in> r"
      with trans y1(3) have "(x1, y2) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x1 = y2") (auto simp: antisym_def)
    next
      assume *: "(y2, y1) \<in> r"
      with trans y2(3) have "(x2, y1) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x2 = y1") (auto simp: antisym_def)
    qed
  qed
qed

lemma Cinfinite_limit_finite: "\<lbrakk>finite X; X \<subseteq> Field r; Cinfinite r\<rbrakk>
 \<Longrightarrow> \<exists>y \<in> Field r. \<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)"
proof (induct X rule: finite_induct)
  case empty thus ?case unfolding cinfinite_def using ex_in_conv[of "Field r"] finite.emptyI by auto
next
  case (insert x X)
  then obtain y where y: "y \<in> Field r" "\<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)" by blast
  then obtain z where z: "z \<in> Field r" "x \<noteq> z \<and> (x, z) \<in> r" "y \<noteq> z \<and> (y, z) \<in> r"
    using Cinfinite_limit2[OF _ y(1) insert(5), of x] insert(4) by blast
  show ?case by (metis Card_order_trans insert(5) insertE y(2) z)
qed

lemma insert_subsetI: "\<lbrakk>x \<in> A; X \<subseteq> A\<rbrakk> \<Longrightarrow> insert x X \<subseteq> A"
by auto

(*helps resolution*)
lemma well_order_induct_imp:
  "wo_rel r \<Longrightarrow> (\<And>x. \<forall>y. y \<noteq> x \<and> (y, x) \<in> r \<longrightarrow> y \<in> Field r \<longrightarrow> P y \<Longrightarrow> x \<in> Field r \<longrightarrow> P x) \<Longrightarrow>
     x \<in> Field r \<longrightarrow> P x"
by (erule wo_rel.well_order_induct)

lemma meta_spec2:
  assumes "(\<And>x y. PROP P x y)"
  shows "PROP P x y"
by (rule `(\<And>x y. PROP P x y)`)

(*Extended List_Prefix*)

definition prefCl where
  "prefCl Kl = (\<forall> kl1 kl2. kl1 \<le> kl2 \<and> kl2 \<in> Kl \<longrightarrow> kl1 \<in> Kl)"
definition PrefCl where
  "PrefCl A n = (\<forall>kl kl'. kl \<in> A n \<and> kl' \<le> kl \<longrightarrow> (\<exists>m\<le>n. kl' \<in> A m))"

lemma prefCl_UN:
  "\<lbrakk>\<And>n. PrefCl A n\<rbrakk> \<Longrightarrow> prefCl (\<Union>n. A n)"
unfolding prefCl_def PrefCl_def by fastforce

definition Succ where "Succ Kl kl = {k . kl @ [k] \<in> Kl}"
definition Shift where "Shift Kl k = {kl. k # kl \<in> Kl}"
definition shift where "shift lab k = (\<lambda>kl. lab (k # kl))"

lemmas sh_def = Shift_def shift_def

lemma empty_Shift: "\<lbrakk>[] \<in> Kl; k \<in> Succ Kl []\<rbrakk> \<Longrightarrow> [] \<in> Shift Kl k"
unfolding Shift_def Succ_def by simp

lemma Shift_clists: "Kl \<subseteq> Field (clists r) \<Longrightarrow> Shift Kl k \<subseteq> Field (clists r)"
unfolding Shift_def clists_def Field_card_of by auto

lemma Shift_prefCl: "prefCl Kl \<Longrightarrow> prefCl (Shift Kl k)"
unfolding prefCl_def Shift_def
proof safe
  fix kl1 kl2
  assume "\<forall>kl1 kl2. kl1 \<le> kl2 \<and> kl2 \<in> Kl \<longrightarrow> kl1 \<in> Kl"
    "kl1 \<le> kl2" "k # kl2 \<in> Kl"
  thus "k # kl1 \<in> Kl" using Cons_prefix_Cons[of k kl1 k kl2] by blast
qed

lemma not_in_Shift: "kl \<notin> Shift Kl x \<Longrightarrow> x # kl \<notin> Kl"
unfolding Shift_def by simp

lemma prefCl_Succ: "\<lbrakk>prefCl Kl; k # kl \<in> Kl\<rbrakk> \<Longrightarrow> k \<in> Succ Kl []"
unfolding Succ_def proof
  assume "prefCl Kl" "k # kl \<in> Kl"
  moreover have "k # [] \<le> k # kl" by auto
  ultimately have "k # [] \<in> Kl" unfolding prefCl_def by blast
  thus "[] @ [k] \<in> Kl" by simp
qed

lemma SuccD: "k \<in> Succ Kl kl \<Longrightarrow> kl @ [k] \<in> Kl"
unfolding Succ_def by simp

lemmas SuccE = SuccD[elim_format]

lemma SuccI: "kl @ [k] \<in> Kl \<Longrightarrow> k \<in> Succ Kl kl"
unfolding Succ_def by simp

lemma ShiftD: "kl \<in> Shift Kl k \<Longrightarrow> k # kl \<in> Kl"
unfolding Shift_def by simp

lemma Succ_Shift: "Succ (Shift Kl k) kl = Succ Kl (k # kl)"
unfolding Succ_def Shift_def by auto

lemma ShiftI: "k # kl \<in> Kl \<Longrightarrow> kl \<in> Shift Kl k"
unfolding Shift_def by simp

lemma Func_cexp: "|Func A B| =o |B| ^c |A|"
unfolding cexp_def Field_card_of by (simp only: card_of_refl)

lemma clists_bound: "A \<in> Field (cpow (clists r)) - {{}} \<Longrightarrow> |A| \<le>o clists r"
unfolding cpow_def clists_def Field_card_of by (auto simp: card_of_mono1)

lemma cpow_clists_czero: "\<lbrakk>A \<in> Field (cpow (clists r)) - {{}}; |A| =o czero\<rbrakk> \<Longrightarrow> False"
unfolding cpow_def clists_def
by (auto simp add: card_of_ordIso_czero_iff_empty[symmetric])
   (erule notE, erule ordIso_transitive, rule czero_ordIso)

lemma incl_UNION_I:
assumes "i \<in> I" and "A \<subseteq> F i"
shows "A \<subseteq> UNION I F"
using assms by auto

lemma Nil_clists: "{[]} \<subseteq> Field (clists r)"
unfolding clists_def Field_card_of by auto

lemma Cons_clists:
  "\<lbrakk>x \<in> Field r; xs \<in> Field (clists r)\<rbrakk> \<Longrightarrow> x # xs \<in> Field (clists r)"
unfolding clists_def Field_card_of by auto

lemma length_Cons: "length (x#xs) = Suc (length xs)"
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
definition pickWP_pred where
"pickWP_pred A p1 p2 b1 b2 a \<equiv>
 a \<in> A \<and> p1 a = b1 \<and> p2 a = b2"

definition pickWP where
"pickWP A p1 p2 b1 b2 \<equiv>
 SOME a. pickWP_pred A p1 p2 b1 b2 a"

lemma pickWP_pred:
assumes "wpull A B1 B2 f1 f2 p1 p2" and
"b1 \<in> B1" and "b2 \<in> B2" and "f1 b1 = f2 b2"
shows "\<exists> a. pickWP_pred A p1 p2 b1 b2 a"
using assms unfolding wpull_def pickWP_pred_def by blast

lemma pickWP_pred_pickWP:
assumes "wpull A B1 B2 f1 f2 p1 p2" and
"b1 \<in> B1" and "b2 \<in> B2" and "f1 b1 = f2 b2"
shows "pickWP_pred A p1 p2 b1 b2 (pickWP A p1 p2 b1 b2)"
unfolding pickWP_def using assms by(rule someI_ex[OF pickWP_pred])

lemma pickWP:
assumes "wpull A B1 B2 f1 f2 p1 p2" and
"b1 \<in> B1" and "b2 \<in> B2" and "f1 b1 = f2 b2"
shows "pickWP A p1 p2 b1 b2 \<in> A"
      "p1 (pickWP A p1 p2 b1 b2) = b1"
      "p2 (pickWP A p1 p2 b1 b2) = b2"
using assms pickWP_pred_pickWP unfolding pickWP_pred_def by fastforce+

lemma ssubst_mem: "\<lbrakk>t = s; s \<in> X\<rbrakk> \<Longrightarrow> t \<in> X" by simp

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

lemma sum_case_cong: "p = q \<Longrightarrow> sum_case f g p = sum_case f g q"
by simp

lemma sum_case_step:
  "sum_case (sum_case f' g') g (Inl p) = sum_case f' g' p"
  "sum_case f (sum_case f' g') (Inr p) = sum_case f' g' p"
by auto

lemma obj_sumE: "\<lbrakk>\<forall>x. s = Inl x \<longrightarrow> P; \<forall>x. s = Inr x \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (cases s) auto

lemma obj_sum_base: "\<lbrakk>\<And>x. s = x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by auto

lemma obj_sum_step:
  "\<lbrakk>\<forall>x. s = f (Inr (Inl x)) \<longrightarrow> P; \<forall>x. s = f (Inr (Inr x)) \<longrightarrow> P\<rbrakk> \<Longrightarrow> \<forall>x. s = f (Inr x) \<longrightarrow> P"
by (metis obj_sumE)

lemma not_arg_cong_Inr: "x \<noteq> y \<Longrightarrow> Inr x \<noteq> Inr y"
by auto

end
