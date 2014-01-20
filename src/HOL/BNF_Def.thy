(*  Title:      HOL/BNF/BNF_Def.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Definition of bounded natural functors.
*)

header {* Definition of Bounded Natural Functors *}

theory BNF_Def
imports BNF_Util
   (*FIXME: register fundef_cong attribute in an interpretation to remove this dependency*)
  FunDef
keywords
  "print_bnfs" :: diag and
  "bnf" :: thy_goal
begin

lemma collect_o: "collect F o g = collect ((\<lambda>f. f o g) ` F)"
  by (rule ext) (auto simp only: o_apply collect_def)

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

lemma convol_mem_GrpI:
"x \<in> A \<Longrightarrow> <id , g> x \<in> (Collect (split (Grp A g)))"
unfolding convol_def Grp_def by auto

definition csquare where
"csquare A f1 f2 p1 p2 \<longleftrightarrow> (\<forall> a \<in> A. f1 (p1 a) = f2 (p2 a))"

lemma eq_alt: "op = = Grp UNIV id"
unfolding Grp_def by auto

lemma leq_conversepI: "R = op = \<Longrightarrow> R \<le> R^--1"
  by auto

lemma leq_OOI: "R = op = \<Longrightarrow> R \<le> R OO R"
  by auto

lemma OO_Grp_alt: "(Grp A f)^--1 OO Grp A g = (\<lambda>x y. \<exists>z. z \<in> A \<and> f z = x \<and> g z = y)"
  unfolding Grp_def by auto

lemma Grp_UNIV_id: "f = id \<Longrightarrow> (Grp UNIV f)^--1 OO Grp UNIV f = Grp UNIV f"
unfolding Grp_def by auto

lemma Grp_UNIV_idI: "x = y \<Longrightarrow> Grp UNIV id x y"
unfolding Grp_def by auto

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

definition "pick_middlep P Q a c = (SOME b. P a b \<and> Q b c)"

lemma pick_middlep:
"(P OO Q) a c \<Longrightarrow> P a (pick_middlep P Q a c) \<and> Q (pick_middlep P Q a c) c"
unfolding pick_middlep_def apply(rule someI_ex) by auto

definition fstOp where "fstOp P Q ac = (fst ac, pick_middlep P Q (fst ac) (snd ac))"
definition sndOp where "sndOp P Q ac = (pick_middlep P Q (fst ac) (snd ac), (snd ac))"

lemma fstOp_in: "ac \<in> Collect (split (P OO Q)) \<Longrightarrow> fstOp P Q ac \<in> Collect (split P)"
unfolding fstOp_def mem_Collect_eq
by (subst (asm) surjective_pairing, unfold prod.cases) (erule pick_middlep[THEN conjunct1])

lemma fst_fstOp: "fst bc = (fst \<circ> fstOp P Q) bc"
unfolding comp_def fstOp_def by simp

lemma snd_sndOp: "snd bc = (snd \<circ> sndOp P Q) bc"
unfolding comp_def sndOp_def by simp

lemma sndOp_in: "ac \<in> Collect (split (P OO Q)) \<Longrightarrow> sndOp P Q ac \<in> Collect (split Q)"
unfolding sndOp_def mem_Collect_eq
by (subst (asm) surjective_pairing, unfold prod.cases) (erule pick_middlep[THEN conjunct2])

lemma csquare_fstOp_sndOp:
"csquare (Collect (split (P OO Q))) snd fst (fstOp P Q) (sndOp P Q)"
unfolding csquare_def fstOp_def sndOp_def using pick_middlep by simp

lemma snd_fst_flip: "snd xy = (fst o (%(x, y). (y, x))) xy"
by (simp split: prod.split)

lemma fst_snd_flip: "fst xy = (snd o (%(x, y). (y, x))) xy"
by (simp split: prod.split)

lemma flip_pred: "A \<subseteq> Collect (split (R ^--1)) \<Longrightarrow> (%(x, y). (y, x)) ` A \<subseteq> Collect (split R)"
by auto

lemma Collect_split_mono: "A \<le> B \<Longrightarrow> Collect (split A) \<subseteq> Collect (split B)"
  by auto

lemma Collect_split_mono_strong: 
  "\<lbrakk>\<forall>a\<in>fst ` A. \<forall>b \<in> snd ` A. P a b \<longrightarrow> Q a b; A \<subseteq> Collect (split P)\<rbrakk> \<Longrightarrow>
  A \<subseteq> Collect (split Q)"
  by fastforce

lemma predicate2_eqD: "A = B \<Longrightarrow> A a b \<longleftrightarrow> B a b"
by metis

lemma sum_case_o_inj:
"sum_case f g \<circ> Inl = f"
"sum_case f g \<circ> Inr = g"
by auto

lemma card_order_csum_cone_cexp_def:
  "card_order r \<Longrightarrow> ( |A1| +c cone) ^c r = |Func UNIV (Inl ` A1 \<union> {Inr ()})|"
  unfolding cexp_def cone_def Field_csum Field_card_of by (auto dest: Field_card_order)

lemma If_the_inv_into_in_Func:
  "\<lbrakk>inj_on g C; C \<subseteq> B \<union> {x}\<rbrakk> \<Longrightarrow>
  (\<lambda>i. if i \<in> g ` C then the_inv_into C g i else x) \<in> Func UNIV (B \<union> {x})"
unfolding Func_def by (auto dest: the_inv_into_into)

lemma If_the_inv_into_f_f:
  "\<lbrakk>i \<in> C; inj_on g C\<rbrakk> \<Longrightarrow>
  ((\<lambda>i. if i \<in> g ` C then the_inv_into C g i else x) o g) i = id i"
unfolding Func_def by (auto elim: the_inv_into_f_f)

definition vimage2p where
  "vimage2p f g R = (\<lambda>x y. R (f x) (g y))"

lemma vimage2pI: "R (f x) (g y) \<Longrightarrow> vimage2p f g R x y"
  unfolding vimage2p_def by -

lemma fun_rel_iff_leq_vimage2p: "(fun_rel R S) f g = (R \<le> vimage2p f g S)"
  unfolding fun_rel_def vimage2p_def by auto

lemma convol_image_vimage2p: "<f o fst, g o snd> ` Collect (split (vimage2p f g R)) \<subseteq> Collect (split R)"
  unfolding vimage2p_def convol_def by auto

lemma vimage2p_Grp: "vimage2p f g P = Grp UNIV f OO P OO (Grp UNIV g)\<inverse>\<inverse>"
  unfolding vimage2p_def Grp_def by auto

(*FIXME: duplicates lemma from Record.thy*)
lemma o_eq_dest_lhs: "a o b = c \<Longrightarrow> a (b v) = c v"
  by clarsimp

ML_file "Tools/bnf_def_tactics.ML"
ML_file "Tools/bnf_def.ML"

end
