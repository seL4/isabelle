(*  Title:      HOL/BNF/BNF_Def.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Definition of bounded natural functors.
*)

header {* Definition of Bounded Natural Functors *}

theory BNF_Def
imports BNF_Util
keywords
  "print_bnfs" :: diag and
  "bnf" :: thy_goal
begin

lemma collect_o: "collect F o g = collect ((\<lambda>f. f o g) ` F)"
by (rule ext) (auto simp only: o_apply collect_def)

lemma converse_mono:
"R1 ^-1 \<subseteq> R2 ^-1 \<longleftrightarrow> R1 \<subseteq> R2"
unfolding converse_def by auto

lemma conversep_mono:
"R1 ^--1 \<le> R2 ^--1 \<longleftrightarrow> R1 \<le> R2"
unfolding conversep.simps by auto

lemma converse_shift:
"R1 \<subseteq> R2 ^-1 \<Longrightarrow> R1 ^-1 \<subseteq> R2"
unfolding converse_def by auto

lemma conversep_shift:
"R1 \<le> R2 ^--1 \<Longrightarrow> R1 ^--1 \<le> R2"
unfolding conversep.simps by auto

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

lemma convol_memI:
"\<lbrakk>f x = f' x; g x = g' x; P x\<rbrakk> \<Longrightarrow> <f , g> x \<in> {(f' a, g' a) |a. P a}"
unfolding convol_def by auto

lemma convol_mem_GrpI:
"\<lbrakk>g x = g' x; x \<in> A\<rbrakk> \<Longrightarrow> <id , g> x \<in> (Collect (split (Grp A g)))"
unfolding convol_def Grp_def by auto

definition csquare where
"csquare A f1 f2 p1 p2 \<longleftrightarrow> (\<forall> a \<in> A. f1 (p1 a) = f2 (p2 a))"

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
  using assms unfolding wppull_def by blast
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
  apply (rule bexI[of _ "j a'"]) unfolding b1 b2 using a' 1 by auto
qed

lemma wppull_id: "\<lbrakk>wpull UNIV UNIV UNIV f1 f2 p1 p2; e1 = id; e2 = id\<rbrakk> \<Longrightarrow>
   wppull UNIV UNIV UNIV f1 f2 e1 e2 p1 p2"
by (erule wpull_wppull) auto

lemma Id_alt: "Id = Gr UNIV id"
unfolding Gr_def by auto

lemma eq_alt: "op = = Grp UNIV id"
unfolding Grp_def by auto

lemma leq_conversepI: "R = op = \<Longrightarrow> R \<le> R^--1"
  by auto

lemma eq_OOI: "R = op = \<Longrightarrow> R = R OO R"
  by auto

lemma Gr_UNIV_id: "f = id \<Longrightarrow> (Gr UNIV f)^-1 O Gr UNIV f = Gr UNIV f"
unfolding Gr_def by auto

lemma Grp_UNIV_id: "f = id \<Longrightarrow> (Grp UNIV f)^--1 OO Grp UNIV f = Grp UNIV f"
unfolding Grp_def by auto

lemma Grp_UNIV_idI: "x = y \<Longrightarrow> Grp UNIV id x y"
unfolding Grp_def by auto

lemma Gr_mono: "A \<subseteq> B \<Longrightarrow> Gr A f \<subseteq> Gr B f"
unfolding Gr_def by auto

lemma Grp_mono: "A \<le> B \<Longrightarrow> Grp A f \<le> Grp B f"
unfolding Grp_def by auto

lemma GrpI: "\<lbrakk>f x = y; x \<in> A\<rbrakk> \<Longrightarrow> Grp A f x y"
unfolding Grp_def by auto

lemma GrpE: "Grp A f x y \<Longrightarrow> (\<lbrakk>f x = y; x \<in> A\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
unfolding Grp_def by auto

lemma Collect_split_Grp_eqD: "z \<in> Collect (split (Grp A f)) \<Longrightarrow> (f \<circ> fst) z = snd z"
unfolding Grp_def o_def by auto

lemma Collect_split_Grp_inD: "z \<in> Collect (split (Grp A f)) \<Longrightarrow> fst z \<in> A"
unfolding Grp_def o_def by auto

lemma wpull_Gr:
"wpull (Gr A f) A (f ` A) f id fst snd"
unfolding wpull_def Gr_def by auto

lemma wpull_Grp:
"wpull (Collect (split (Grp A f))) A (f ` A) f id fst snd"
unfolding wpull_def Grp_def by auto

definition "pick_middle P Q a c = (SOME b. (a,b) \<in> P \<and> (b,c) \<in> Q)"

definition "pick_middlep P Q a c = (SOME b. P a b \<and> Q b c)"

lemma pick_middle:
"(a,c) \<in> P O Q \<Longrightarrow> (a, pick_middle P Q a c) \<in> P \<and> (pick_middle P Q a c, c) \<in> Q"
unfolding pick_middle_def apply(rule someI_ex) by auto

lemma pick_middlep:
"(P OO Q) a c \<Longrightarrow> P a (pick_middlep P Q a c) \<and> Q (pick_middlep P Q a c) c"
unfolding pick_middlep_def apply(rule someI_ex) by auto

definition fstO where "fstO P Q ac = (fst ac, pick_middle P Q (fst ac) (snd ac))"
definition sndO where "sndO P Q ac = (pick_middle P Q (fst ac) (snd ac), snd ac)"

definition fstOp where "fstOp P Q ac = (fst ac, pick_middlep P Q (fst ac) (snd ac))"
definition sndOp where "sndOp P Q ac = (pick_middlep P Q (fst ac) (snd ac), (snd ac))"

lemma fstO_in: "ac \<in> P O Q \<Longrightarrow> fstO P Q ac \<in> P"
unfolding fstO_def by (subst (asm) surjective_pairing) (rule pick_middle[THEN conjunct1])

lemma fstOp_in: "ac \<in> Collect (split (P OO Q)) \<Longrightarrow> fstOp P Q ac \<in> Collect (split P)"
unfolding fstOp_def mem_Collect_eq
by (subst (asm) surjective_pairing, unfold prod.cases) (erule pick_middlep[THEN conjunct1])

lemma fst_fstO: "fst bc = (fst \<circ> fstO P Q) bc"
unfolding comp_def fstO_def by simp

lemma fst_fstOp: "fst bc = (fst \<circ> fstOp P Q) bc"
unfolding comp_def fstOp_def by simp

lemma snd_sndO: "snd bc = (snd \<circ> sndO P Q) bc"
unfolding comp_def sndO_def by simp

lemma snd_sndOp: "snd bc = (snd \<circ> sndOp P Q) bc"
unfolding comp_def sndOp_def by simp

lemma sndO_in: "ac \<in> P O Q \<Longrightarrow> sndO P Q ac \<in> Q"
unfolding sndO_def
by (subst (asm) surjective_pairing) (rule pick_middle[THEN conjunct2])

lemma sndOp_in: "ac \<in> Collect (split (P OO Q)) \<Longrightarrow> sndOp P Q ac \<in> Collect (split Q)"
unfolding sndOp_def mem_Collect_eq
by (subst (asm) surjective_pairing, unfold prod.cases) (erule pick_middlep[THEN conjunct2])

lemma csquare_fstO_sndO:
"csquare (P O Q) snd fst (fstO P Q) (sndO P Q)"
unfolding csquare_def fstO_def sndO_def using pick_middle by simp

lemma csquare_fstOp_sndOp:
"csquare (Collect (split (P OO Q))) snd fst (fstOp P Q) (sndOp P Q)"
unfolding csquare_def fstOp_def sndOp_def using pick_middlep by simp

lemma wppull_fstO_sndO:
shows "wppull (P O Q) P Q snd fst fst snd (fstO P Q) (sndO P Q)"
using pick_middle unfolding wppull_def fstO_def sndO_def relcomp_def by auto

lemma wppull_fstOp_sndOp:
shows "wppull (Collect (split (P OO Q))) (Collect (split P)) (Collect (split Q)) snd fst fst snd (fstOp P Q) (sndOp P Q)"
using pick_middlep unfolding wppull_def fstOp_def sndOp_def relcompp.simps by auto

lemma snd_fst_flip: "snd xy = (fst o (%(x, y). (y, x))) xy"
by (simp split: prod.split)

lemma fst_snd_flip: "fst xy = (snd o (%(x, y). (y, x))) xy"
by (simp split: prod.split)

lemma flip_rel: "A \<subseteq> (R ^-1) \<Longrightarrow> (%(x, y). (y, x)) ` A \<subseteq> R"
by auto

lemma flip_pred: "A \<subseteq> Collect (split (R ^--1)) \<Longrightarrow> (%(x, y). (y, x)) ` A \<subseteq> Collect (split R)"
by auto

lemma pointfreeE: "f o g = f' o g' \<Longrightarrow> f (g x) = f' (g' x)"
unfolding o_def fun_eq_iff by simp

lemma Collect_split_mono: "A \<le> B \<Longrightarrow> Collect (split A) \<subseteq> Collect (split B)"
  by auto

lemma predicate2_cong: "A = B \<Longrightarrow> A a b \<longleftrightarrow> B a b"
by metis

lemma fun_cong_pair: "f = g \<Longrightarrow> f {(a, b). R a b} = g {(a, b). R a b}"
by (rule fun_cong)

lemma flip_as_converse: "{(a, b). R b a} = converse {(a, b). R a b}"
unfolding converse_def mem_Collect_eq prod.cases
apply (rule arg_cong[of _ _ "\<lambda>x. Collect (prod_case x)"])
apply (rule ext)+
apply (unfold conversep_iff)
by (rule refl)

ML_file "Tools/bnf_def_tactics.ML"
ML_file "Tools/bnf_def.ML"


end
