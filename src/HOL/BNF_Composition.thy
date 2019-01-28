(*  Title:      HOL/BNF_Composition.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013, 2014

Composition of bounded natural functors.
*)

section \<open>Composition of Bounded Natural Functors\<close>

theory BNF_Composition
imports BNF_Def
keywords
  "copy_bnf" :: thy_decl and
  "lift_bnf" :: thy_goal
begin

lemma ssubst_mem: "\<lbrakk>t = s; s \<in> X\<rbrakk> \<Longrightarrow> t \<in> X"
  by simp

lemma empty_natural: "(\<lambda>_. {}) \<circ> f = image g \<circ> (\<lambda>_. {})"
  by (rule ext) simp

lemma Union_natural: "Union \<circ> image (image f) = image f \<circ> Union"
  by (rule ext) (auto simp only: comp_apply)

lemma in_Union_o_assoc: "x \<in> (Union \<circ> gset \<circ> gmap) A \<Longrightarrow> x \<in> (Union \<circ> (gset \<circ> gmap)) A"
  by (unfold comp_assoc)

lemma comp_single_set_bd:
  assumes fbd_Card_order: "Card_order fbd" and
    fset_bd: "\<And>x. |fset x| \<le>o fbd" and
    gset_bd: "\<And>x. |gset x| \<le>o gbd"
  shows "|\<Union>(fset ` gset x)| \<le>o gbd *c fbd"
  apply simp
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

lemma csum_dup: "cinfinite r \<Longrightarrow> Card_order r \<Longrightarrow> p +c p' =o r +c r \<Longrightarrow> p +c p' =o r"
  apply (erule ordIso_transitive)
  apply (frule csum_absorb2')
  apply (erule ordLeq_refl)
  by simp

lemma cprod_dup: "cinfinite r \<Longrightarrow> Card_order r \<Longrightarrow> p *c p' =o r *c r \<Longrightarrow> p *c p' =o r"
  apply (erule ordIso_transitive)
  apply (rule cprod_infinite)
  by simp

lemma Union_image_insert: "\<Union>(f ` insert a B) = f a \<union> \<Union>(f ` B)"
  by simp

lemma Union_image_empty: "A \<union> \<Union>(f ` {}) = A"
  by simp

lemma image_o_collect: "collect ((\<lambda>f. image g \<circ> f) ` F) = image g \<circ> collect F"
  by (rule ext) (auto simp add: collect_def)

lemma conj_subset_def: "A \<subseteq> {x. P x \<and> Q x} = (A \<subseteq> {x. P x} \<and> A \<subseteq> {x. Q x})"
  by blast

lemma UN_image_subset: "\<Union>(f ` g x) \<subseteq> X = (g x \<subseteq> {x. f x \<subseteq> X})"
  by blast

lemma comp_set_bd_Union_o_collect: "|\<Union>(\<Union>((\<lambda>f. f x) ` X))| \<le>o hbd \<Longrightarrow> |(Union \<circ> collect X) x| \<le>o hbd"
  by (unfold comp_apply collect_def) simp

lemma Collect_inj: "Collect P = Collect Q \<Longrightarrow> P = Q"
  by blast

lemma Grp_fst_snd: "(Grp (Collect (case_prod R)) fst)\<inverse>\<inverse> OO Grp (Collect (case_prod R)) snd = R"
  unfolding Grp_def fun_eq_iff relcompp.simps by auto

lemma OO_Grp_cong: "A = B \<Longrightarrow> (Grp A f)\<inverse>\<inverse> OO Grp A g = (Grp B f)\<inverse>\<inverse> OO Grp B g"
  by (rule arg_cong)

lemma vimage2p_relcompp_mono: "R OO S \<le> T \<Longrightarrow>
  vimage2p f g R OO vimage2p g h S \<le> vimage2p f h T"
  unfolding vimage2p_def by auto

lemma type_copy_map_cong0: "M (g x) = N (h x) \<Longrightarrow> (f \<circ> M \<circ> g) x = (f \<circ> N \<circ> h) x"
  by auto

lemma type_copy_set_bd: "(\<And>y. |S y| \<le>o bd) \<Longrightarrow> |(S \<circ> Rep) x| \<le>o bd"
  by auto

lemma vimage2p_cong: "R = S \<Longrightarrow> vimage2p f g R = vimage2p f g S"
  by simp

lemma Ball_comp_iff: "(\<lambda>x. Ball (A x) f) \<circ> g = (\<lambda>x. Ball ((A \<circ> g) x) f)"
  unfolding o_def by auto

lemma conj_comp_iff: "(\<lambda>x. P x \<and> Q x) \<circ> g = (\<lambda>x. (P \<circ> g) x \<and> (Q \<circ> g) x)"
  unfolding o_def by auto

context
  fixes Rep Abs
  assumes type_copy: "type_definition Rep Abs UNIV"
begin

lemma type_copy_map_id0: "M = id \<Longrightarrow> Abs \<circ> M \<circ> Rep = id"
  using type_definition.Rep_inverse[OF type_copy] by auto

lemma type_copy_map_comp0: "M = M1 \<circ> M2 \<Longrightarrow> f \<circ> M \<circ> g = (f \<circ> M1 \<circ> Rep) \<circ> (Abs \<circ> M2 \<circ> g)"
  using type_definition.Abs_inverse[OF type_copy UNIV_I] by auto

lemma type_copy_set_map0: "S \<circ> M = image f \<circ> S' \<Longrightarrow> (S \<circ> Rep) \<circ> (Abs \<circ> M \<circ> g) = image f \<circ> (S' \<circ> g)"
  using type_definition.Abs_inverse[OF type_copy UNIV_I] by (auto simp: o_def fun_eq_iff)

lemma type_copy_wit: "x \<in> (S \<circ> Rep) (Abs y) \<Longrightarrow> x \<in> S y"
  using type_definition.Abs_inverse[OF type_copy UNIV_I] by auto

lemma type_copy_vimage2p_Grp_Rep: "vimage2p f Rep (Grp (Collect P) h) =
    Grp (Collect (\<lambda>x. P (f x))) (Abs \<circ> h \<circ> f)"
  unfolding vimage2p_def Grp_def fun_eq_iff
  by (auto simp: type_definition.Abs_inverse[OF type_copy UNIV_I]
   type_definition.Rep_inverse[OF type_copy] dest: sym)

lemma type_copy_vimage2p_Grp_Abs:
  "\<And>h. vimage2p g Abs (Grp (Collect P) h) = Grp (Collect (\<lambda>x. P (g x))) (Rep \<circ> h \<circ> g)"
  unfolding vimage2p_def Grp_def fun_eq_iff
  by (auto simp: type_definition.Abs_inverse[OF type_copy UNIV_I]
   type_definition.Rep_inverse[OF type_copy] dest: sym)

lemma type_copy_ex_RepI: "(\<exists>b. F b) = (\<exists>b. F (Rep b))"
proof safe
  fix b assume "F b"
  show "\<exists>b'. F (Rep b')"
  proof (rule exI)
    from \<open>F b\<close> show "F (Rep (Abs b))" using type_definition.Abs_inverse[OF type_copy] by auto
  qed
qed blast

lemma vimage2p_relcompp_converse:
  "vimage2p f g (R\<inverse>\<inverse> OO S) = (vimage2p Rep f R)\<inverse>\<inverse> OO vimage2p Rep g S"
  unfolding vimage2p_def relcompp.simps conversep.simps fun_eq_iff image_def
  by (auto simp: type_copy_ex_RepI)

end

bnf DEADID: 'a
  map: "id :: 'a \<Rightarrow> 'a"
  bd: natLeq
  rel: "(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  by (auto simp add: natLeq_card_order natLeq_cinfinite)

definition id_bnf :: "'a \<Rightarrow> 'a" where
  "id_bnf \<equiv> (\<lambda>x. x)"

lemma id_bnf_apply: "id_bnf x = x"
  unfolding id_bnf_def by simp

bnf ID: 'a
  map: "id_bnf :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  sets: "\<lambda>x. {x}"
  bd: natLeq
  rel: "id_bnf :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  pred: "id_bnf :: ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  unfolding id_bnf_def
  apply (auto simp: Grp_def fun_eq_iff relcompp.simps natLeq_card_order natLeq_cinfinite)
  apply (rule ordLess_imp_ordLeq[OF finite_ordLess_infinite[OF _ natLeq_Well_order]])
  apply (auto simp add: Field_card_of Field_natLeq card_of_well_order_on)[3]
  done

lemma type_definition_id_bnf_UNIV: "type_definition id_bnf id_bnf UNIV"
  unfolding id_bnf_def by unfold_locales auto

ML_file \<open>Tools/BNF/bnf_comp_tactics.ML\<close>
ML_file \<open>Tools/BNF/bnf_comp.ML\<close>
ML_file \<open>Tools/BNF/bnf_lift.ML\<close>

hide_fact
  DEADID.inj_map DEADID.inj_map_strong DEADID.map_comp DEADID.map_cong DEADID.map_cong0
  DEADID.map_cong_simp DEADID.map_id DEADID.map_id0 DEADID.map_ident DEADID.map_transfer
  DEADID.rel_Grp DEADID.rel_compp DEADID.rel_compp_Grp DEADID.rel_conversep DEADID.rel_eq
  DEADID.rel_flip DEADID.rel_map DEADID.rel_mono DEADID.rel_transfer
  ID.inj_map ID.inj_map_strong ID.map_comp ID.map_cong ID.map_cong0 ID.map_cong_simp ID.map_id
  ID.map_id0 ID.map_ident ID.map_transfer ID.rel_Grp ID.rel_compp ID.rel_compp_Grp ID.rel_conversep
  ID.rel_eq ID.rel_flip ID.rel_map ID.rel_mono ID.rel_transfer ID.set_map ID.set_transfer

end
