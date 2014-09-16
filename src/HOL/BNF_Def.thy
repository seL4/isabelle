(*  Title:      HOL/BNF_Def.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013, 2014

Definition of bounded natural functors.
*)

header {* Definition of Bounded Natural Functors *}

theory BNF_Def
imports BNF_Cardinal_Arithmetic Fun_Def_Base
keywords
  "print_bnfs" :: diag and
  "bnf" :: thy_goal
begin

lemma Collect_splitD: "x \<in> Collect (split A) \<Longrightarrow> A (fst x) (snd x)"
  by auto

definition
  rel_fun :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> bool"
where
  "rel_fun A B = (\<lambda>f g. \<forall>x y. A x y \<longrightarrow> B (f x) (g y))"

lemma rel_funI [intro]:
  assumes "\<And>x y. A x y \<Longrightarrow> B (f x) (g y)"
  shows "rel_fun A B f g"
  using assms by (simp add: rel_fun_def)

lemma rel_funD:
  assumes "rel_fun A B f g" and "A x y"
  shows "B (f x) (g y)"
  using assms by (simp add: rel_fun_def)

definition rel_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_set R = (\<lambda>A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y))"

lemma rel_setI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. R x y"
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x\<in>A. R x y"
  shows "rel_set R A B"
  using assms unfolding rel_set_def by simp

lemma predicate2_transferD:
   "\<lbrakk>rel_fun R1 (rel_fun R2 (op =)) P Q; a \<in> A; b \<in> B; A \<subseteq> {(x, y). R1 x y}; B \<subseteq> {(x, y). R2 x y}\<rbrakk> \<Longrightarrow>
   P (fst a) (fst b) \<longleftrightarrow> Q (snd a) (snd b)"
  unfolding rel_fun_def by (blast dest!: Collect_splitD)

definition collect where
  "collect F x = (\<Union>f \<in> F. f x)"

lemma fstI: "x = (y, z) \<Longrightarrow> fst x = y"
  by simp

lemma sndI: "x = (y, z) \<Longrightarrow> snd x = z"
  by simp

lemma bijI': "\<lbrakk>\<And>x y. (f x = f y) = (x = y); \<And>y. \<exists>x. y = f x\<rbrakk> \<Longrightarrow> bij f"
  unfolding bij_def inj_on_def by auto blast

(* Operator: *)
definition "Gr A f = {(a, f a) | a. a \<in> A}"

definition "Grp A f = (\<lambda>a b. b = f a \<and> a \<in> A)"

definition vimage2p where
  "vimage2p f g R = (\<lambda>x y. R (f x) (g y))"

lemma collect_comp: "collect F \<circ> g = collect ((\<lambda>f. f \<circ> g) ` F)"
  by (rule ext) (auto simp only: comp_apply collect_def)

definition convol ("\<langle>(_,/ _)\<rangle>") where
  "\<langle>f, g\<rangle> \<equiv> \<lambda>a. (f a, g a)"

lemma fst_convol: "fst \<circ> \<langle>f, g\<rangle> = f"
  apply(rule ext)
  unfolding convol_def by simp

lemma snd_convol: "snd \<circ> \<langle>f, g\<rangle> = g"
  apply(rule ext)
  unfolding convol_def by simp

lemma convol_mem_GrpI:
  "x \<in> A \<Longrightarrow> \<langle>id, g\<rangle> x \<in> (Collect (split (Grp A g)))"
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
  unfolding Grp_def comp_def by auto

lemma Collect_split_Grp_inD: "z \<in> Collect (split (Grp A f)) \<Longrightarrow> fst z \<in> A"
  unfolding Grp_def comp_def by auto

definition "pick_middlep P Q a c = (SOME b. P a b \<and> Q b c)"

lemma pick_middlep:
  "(P OO Q) a c \<Longrightarrow> P a (pick_middlep P Q a c) \<and> Q (pick_middlep P Q a c) c"
  unfolding pick_middlep_def apply(rule someI_ex) by auto

definition fstOp where
  "fstOp P Q ac = (fst ac, pick_middlep P Q (fst ac) (snd ac))"

definition sndOp where
  "sndOp P Q ac = (pick_middlep P Q (fst ac) (snd ac), (snd ac))"

lemma fstOp_in: "ac \<in> Collect (split (P OO Q)) \<Longrightarrow> fstOp P Q ac \<in> Collect (split P)"
  unfolding fstOp_def mem_Collect_eq
  by (subst (asm) surjective_pairing, unfold prod.case) (erule pick_middlep[THEN conjunct1])

lemma fst_fstOp: "fst bc = (fst \<circ> fstOp P Q) bc"
  unfolding comp_def fstOp_def by simp

lemma snd_sndOp: "snd bc = (snd \<circ> sndOp P Q) bc"
  unfolding comp_def sndOp_def by simp

lemma sndOp_in: "ac \<in> Collect (split (P OO Q)) \<Longrightarrow> sndOp P Q ac \<in> Collect (split Q)"
  unfolding sndOp_def mem_Collect_eq
  by (subst (asm) surjective_pairing, unfold prod.case) (erule pick_middlep[THEN conjunct2])

lemma csquare_fstOp_sndOp:
  "csquare (Collect (split (P OO Q))) snd fst (fstOp P Q) (sndOp P Q)"
  unfolding csquare_def fstOp_def sndOp_def using pick_middlep by simp

lemma snd_fst_flip: "snd xy = (fst \<circ> (%(x, y). (y, x))) xy"
  by (simp split: prod.split)

lemma fst_snd_flip: "fst xy = (snd \<circ> (%(x, y). (y, x))) xy"
  by (simp split: prod.split)

lemma flip_pred: "A \<subseteq> Collect (split (R ^--1)) \<Longrightarrow> (%(x, y). (y, x)) ` A \<subseteq> Collect (split R)"
  by auto

lemma Collect_split_mono: "A \<le> B \<Longrightarrow> Collect (split A) \<subseteq> Collect (split B)"
  by auto

lemma Collect_split_mono_strong: 
  "\<lbrakk>X = fst ` A; Y = snd ` A; \<forall>a\<in>X. \<forall>b \<in> Y. P a b \<longrightarrow> Q a b; A \<subseteq> Collect (split P)\<rbrakk> \<Longrightarrow>
   A \<subseteq> Collect (split Q)"
  by fastforce


lemma predicate2_eqD: "A = B \<Longrightarrow> A a b \<longleftrightarrow> B a b"
  by simp

lemma case_sum_o_inj: "case_sum f g \<circ> Inl = f" "case_sum f g \<circ> Inr = g"
  by auto

lemma map_sum_o_inj: "map_sum f g o Inl = Inl o f" "map_sum f g o Inr = Inr o g"
  by auto

lemma card_order_csum_cone_cexp_def:
  "card_order r \<Longrightarrow> ( |A1| +c cone) ^c r = |Func UNIV (Inl ` A1 \<union> {Inr ()})|"
  unfolding cexp_def cone_def Field_csum Field_card_of by (auto dest: Field_card_order)

lemma If_the_inv_into_in_Func:
  "\<lbrakk>inj_on g C; C \<subseteq> B \<union> {x}\<rbrakk> \<Longrightarrow>
   (\<lambda>i. if i \<in> g ` C then the_inv_into C g i else x) \<in> Func UNIV (B \<union> {x})"
  unfolding Func_def by (auto dest: the_inv_into_into)

lemma If_the_inv_into_f_f:
  "\<lbrakk>i \<in> C; inj_on g C\<rbrakk> \<Longrightarrow> ((\<lambda>i. if i \<in> g ` C then the_inv_into C g i else x) \<circ> g) i = id i"
  unfolding Func_def by (auto elim: the_inv_into_f_f)

lemma the_inv_f_o_f_id: "inj f \<Longrightarrow> (the_inv f \<circ> f) z = id z"
  by (simp add: the_inv_f_f)

lemma vimage2pI: "R (f x) (g y) \<Longrightarrow> vimage2p f g R x y"
  unfolding vimage2p_def by -

lemma rel_fun_iff_leq_vimage2p: "(rel_fun R S) f g = (R \<le> vimage2p f g S)"
  unfolding rel_fun_def vimage2p_def by auto

lemma convol_image_vimage2p: "\<langle>f \<circ> fst, g \<circ> snd\<rangle> ` Collect (split (vimage2p f g R)) \<subseteq> Collect (split R)"
  unfolding vimage2p_def convol_def by auto

lemma vimage2p_Grp: "vimage2p f g P = Grp UNIV f OO P OO (Grp UNIV g)\<inverse>\<inverse>"
  unfolding vimage2p_def Grp_def by auto

lemma subst_Pair: "P x y \<Longrightarrow> a = (x, y) \<Longrightarrow> P (fst a) (snd a)"
  by simp

lemma comp_apply_eq: "f (g x) = h (k x) \<Longrightarrow> (f \<circ> g) x = (h \<circ> k) x"
  unfolding comp_apply by assumption

ML_file "Tools/BNF/bnf_util.ML"
ML_file "Tools/BNF/bnf_tactics.ML"
ML_file "Tools/BNF/bnf_def_tactics.ML"
ML_file "Tools/BNF/bnf_def.ML"

end
