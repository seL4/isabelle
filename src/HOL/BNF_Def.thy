(*  Title:      HOL/BNF_Def.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013, 2014

Definition of bounded natural functors.
*)

section \<open>Definition of Bounded Natural Functors\<close>

theory BNF_Def
imports BNF_Cardinal_Arithmetic Fun_Def_Base
keywords
  "print_bnfs" :: diag and
  "bnf" :: thy_goal_defn
begin

lemma Collect_case_prodD: "x \<in> Collect (case_prod A) \<Longrightarrow> A (fst x) (snd x)"
  by auto

inductive
   rel_sum :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'c + 'd \<Rightarrow> bool" for R1 R2
where
  "R1 a c \<Longrightarrow> rel_sum R1 R2 (Inl a) (Inl c)"
| "R2 b d \<Longrightarrow> rel_sum R1 R2 (Inr b) (Inr d)"

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

lemma rel_fun_mono:
  "\<lbrakk> rel_fun X A f g; \<And>x y. Y x y \<longrightarrow> X x y; \<And>x y. A x y \<Longrightarrow> B x y \<rbrakk> \<Longrightarrow> rel_fun Y B f g"
by(simp add: rel_fun_def)

lemma rel_fun_mono' [mono]:
  "\<lbrakk> \<And>x y. Y x y \<longrightarrow> X x y; \<And>x y. A x y \<longrightarrow> B x y \<rbrakk> \<Longrightarrow> rel_fun X A f g \<longrightarrow> rel_fun Y B f g"
by(simp add: rel_fun_def)

definition rel_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_set R = (\<lambda>A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y))"

lemma rel_setI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. R x y"
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x\<in>A. R x y"
  shows "rel_set R A B"
  using assms unfolding rel_set_def by simp

lemma predicate2_transferD:
   "\<lbrakk>rel_fun R1 (rel_fun R2 (=)) P Q; a \<in> A; b \<in> B; A \<subseteq> {(x, y). R1 x y}; B \<subseteq> {(x, y). R2 x y}\<rbrakk> \<Longrightarrow>
   P (fst a) (fst b) \<longleftrightarrow> Q (snd a) (snd b)"
  unfolding rel_fun_def by (blast dest!: Collect_case_prodD)

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
  by (rule ext) (simp add: collect_def)

definition convol (\<open>\<langle>(_,/ _)\<rangle>\<close>) where
  "\<langle>f, g\<rangle> \<equiv> \<lambda>a. (f a, g a)"

lemma fst_convol: "fst \<circ> \<langle>f, g\<rangle> = f"
  apply(rule ext)
  unfolding convol_def by simp

lemma snd_convol: "snd \<circ> \<langle>f, g\<rangle> = g"
  apply(rule ext)
  unfolding convol_def by simp

lemma convol_mem_GrpI:
  "x \<in> A \<Longrightarrow> \<langle>id, g\<rangle> x \<in> (Collect (case_prod (Grp A g)))"
  unfolding convol_def Grp_def by auto

definition csquare where
  "csquare A f1 f2 p1 p2 \<longleftrightarrow> (\<forall> a \<in> A. f1 (p1 a) = f2 (p2 a))"

lemma eq_alt: "(=) = Grp UNIV id"
  unfolding Grp_def by auto

lemma leq_conversepI: "R = (=) \<Longrightarrow> R \<le> R\<inverse>\<inverse>"
  by auto

lemma leq_OOI: "R = (=) \<Longrightarrow> R \<le> R OO R"
  by auto

lemma OO_Grp_alt: "(Grp A f)\<inverse>\<inverse> OO Grp A g = (\<lambda>x y. \<exists>z. z \<in> A \<and> f z = x \<and> g z = y)"
  unfolding Grp_def by auto

lemma Grp_UNIV_id: "f = id \<Longrightarrow> (Grp UNIV f)\<inverse>\<inverse> OO Grp UNIV f = Grp UNIV f"
  unfolding Grp_def by auto

lemma Grp_UNIV_idI: "x = y \<Longrightarrow> Grp UNIV id x y"
  unfolding Grp_def by auto

lemma Grp_mono: "A \<le> B \<Longrightarrow> Grp A f \<le> Grp B f"
  unfolding Grp_def by auto

lemma GrpI: "\<lbrakk>f x = y; x \<in> A\<rbrakk> \<Longrightarrow> Grp A f x y"
  unfolding Grp_def by auto

lemma GrpE: "Grp A f x y \<Longrightarrow> (\<lbrakk>f x = y; x \<in> A\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding Grp_def by auto

lemma Collect_case_prod_Grp_eqD: "z \<in> Collect (case_prod (Grp A f)) \<Longrightarrow> (f \<circ> fst) z = snd z"
  unfolding Grp_def comp_def by auto

lemma Collect_case_prod_Grp_in: "z \<in> Collect (case_prod (Grp A f)) \<Longrightarrow> fst z \<in> A"
  unfolding Grp_def comp_def by auto

definition "pick_middlep P Q a c = (SOME b. P a b \<and> Q b c)"

lemma pick_middlep:
  "(P OO Q) a c \<Longrightarrow> P a (pick_middlep P Q a c) \<and> Q (pick_middlep P Q a c) c"
  unfolding pick_middlep_def by (rule someI_ex) auto

definition fstOp where
  "fstOp P Q ac = (fst ac, pick_middlep P Q (fst ac) (snd ac))"

definition sndOp where
  "sndOp P Q ac = (pick_middlep P Q (fst ac) (snd ac), (snd ac))"

lemma fstOp_in: "ac \<in> Collect (case_prod (P OO Q)) \<Longrightarrow> fstOp P Q ac \<in> Collect (case_prod P)"
  unfolding fstOp_def mem_Collect_eq
  by (subst (asm) surjective_pairing, unfold prod.case) (erule pick_middlep[THEN conjunct1])

lemma fst_fstOp: "fst bc = (fst \<circ> fstOp P Q) bc"
  unfolding comp_def fstOp_def by simp

lemma snd_sndOp: "snd bc = (snd \<circ> sndOp P Q) bc"
  unfolding comp_def sndOp_def by simp

lemma sndOp_in: "ac \<in> Collect (case_prod (P OO Q)) \<Longrightarrow> sndOp P Q ac \<in> Collect (case_prod Q)"
  unfolding sndOp_def mem_Collect_eq
  by (subst (asm) surjective_pairing, unfold prod.case) (erule pick_middlep[THEN conjunct2])

lemma csquare_fstOp_sndOp:
  "csquare (Collect (f (P OO Q))) snd fst (fstOp P Q) (sndOp P Q)"
  unfolding csquare_def fstOp_def sndOp_def using pick_middlep by simp

lemma snd_fst_flip: "snd xy = (fst \<circ> (%(x, y). (y, x))) xy"
  by (simp split: prod.split)

lemma fst_snd_flip: "fst xy = (snd \<circ> (%(x, y). (y, x))) xy"
  by (simp split: prod.split)

lemma flip_pred: "A \<subseteq> Collect (case_prod (R \<inverse>\<inverse>)) \<Longrightarrow> (%(x, y). (y, x)) ` A \<subseteq> Collect (case_prod R)"
  by auto

lemma predicate2_eqD: "A = B \<Longrightarrow> A a b \<longleftrightarrow> B a b"
  by simp

lemma case_sum_o_inj: "case_sum f g \<circ> Inl = f" "case_sum f g \<circ> Inr = g"
  by auto

lemma map_sum_o_inj: "map_sum f g \<circ> Inl = Inl \<circ> f" "map_sum f g \<circ> Inr = Inr \<circ> g"
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
  unfolding vimage2p_def .

lemma rel_fun_iff_leq_vimage2p: "(rel_fun R S) f g = (R \<le> vimage2p f g S)"
  unfolding rel_fun_def vimage2p_def by auto

lemma convol_image_vimage2p: "\<langle>f \<circ> fst, g \<circ> snd\<rangle> ` Collect (case_prod (vimage2p f g R)) \<subseteq> Collect (case_prod R)"
  unfolding vimage2p_def convol_def by auto

lemma vimage2p_Grp: "vimage2p f g P = Grp UNIV f OO P OO (Grp UNIV g)\<inverse>\<inverse>"
  unfolding vimage2p_def Grp_def by auto

lemma subst_Pair: "P x y \<Longrightarrow> a = (x, y) \<Longrightarrow> P (fst a) (snd a)"
  by simp

lemma comp_apply_eq: "f (g x) = h (k x) \<Longrightarrow> (f \<circ> g) x = (h \<circ> k) x"
  unfolding comp_apply by assumption

lemma refl_ge_eq: "(\<And>x. R x x) \<Longrightarrow> (=) \<le> R"
  by auto

lemma ge_eq_refl: "(=) \<le> R \<Longrightarrow> R x x"
  by auto

lemma reflp_eq: "reflp R = ((=) \<le> R)"
  by (auto simp: reflp_def fun_eq_iff)

lemma transp_relcompp: "transp r \<longleftrightarrow> r OO r \<le> r"
  by (auto simp: transp_def)

lemma symp_conversep: "symp R = (R\<inverse>\<inverse> \<le> R)"
  by (auto simp: symp_def fun_eq_iff)

lemma diag_imp_eq_le: "(\<And>x. x \<in> A \<Longrightarrow> R x x) \<Longrightarrow> \<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x = y \<longrightarrow> R x y"
  by blast

definition eq_onp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "eq_onp R = (\<lambda>x y. R x \<and> x = y)"

lemma eq_onp_Grp: "eq_onp P = BNF_Def.Grp (Collect P) id"
  unfolding eq_onp_def Grp_def by auto

lemma eq_onp_to_eq: "eq_onp P x y \<Longrightarrow> x = y"
  by (simp add: eq_onp_def)

lemma eq_onp_top_eq_eq: "eq_onp top = (=)"
  by (simp add: eq_onp_def)

lemma eq_onp_same_args: "eq_onp P x x = P x"
  by (auto simp add: eq_onp_def)

lemma eq_onp_eqD: "eq_onp P = Q \<Longrightarrow> P x = Q x x"
  unfolding eq_onp_def by blast

lemma Ball_Collect: "Ball A P = (A \<subseteq> (Collect P))"
  by auto

lemma eq_onp_mono0: "\<forall>x\<in>A. P x \<longrightarrow> Q x \<Longrightarrow> \<forall>x\<in>A. \<forall>y\<in>A. eq_onp P x y \<longrightarrow> eq_onp Q x y"
  unfolding eq_onp_def by auto

lemma eq_onp_True: "eq_onp (\<lambda>_. True) = (=)"
  unfolding eq_onp_def by simp

lemma Ball_image_comp: "Ball (f ` A) g = Ball A (g \<circ> f)"
  by auto

lemma rel_fun_Collect_case_prodD:
  "rel_fun A B f g \<Longrightarrow> X \<subseteq> Collect (case_prod A) \<Longrightarrow> x \<in> X \<Longrightarrow> B ((f \<circ> fst) x) ((g \<circ> snd) x)"
  unfolding rel_fun_def by auto

lemma eq_onp_mono_iff: "eq_onp P \<le> eq_onp Q \<longleftrightarrow> P \<le> Q"
  unfolding eq_onp_def by auto

ML_file \<open>Tools/BNF/bnf_util.ML\<close>
ML_file \<open>Tools/BNF/bnf_tactics.ML\<close>
ML_file \<open>Tools/BNF/bnf_def_tactics.ML\<close>
ML_file \<open>Tools/BNF/bnf_def.ML\<close>

end
