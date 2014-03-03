(*  Title:      HOL/BNF_Comp.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

header {* Composition of Bounded Natural Functors *}

theory BNF_Comp
imports Basic_BNFs
begin

lemma empty_natural: "(\<lambda>_. {}) o f = image g o (\<lambda>_. {})"
by (rule ext) simp

lemma Union_natural: "Union o image (image f) = image f o Union"
by (rule ext) (auto simp only: comp_apply)

lemma in_Union_o_assoc: "x \<in> (Union o gset o gmap) A \<Longrightarrow> x \<in> (Union o (gset o gmap)) A"
by (unfold comp_assoc)

lemma comp_single_set_bd:
  assumes fbd_Card_order: "Card_order fbd" and
    fset_bd: "\<And>x. |fset x| \<le>o fbd" and
    gset_bd: "\<And>x. |gset x| \<le>o gbd"
  shows "|\<Union>(fset ` gset x)| \<le>o gbd *c fbd"
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

lemma Union_image_insert: "\<Union>(f ` insert a B) = f a \<union> \<Union>(f ` B)"
by simp

lemma Union_image_empty: "A \<union> \<Union>(f ` {}) = A"
by simp

lemma image_o_collect: "collect ((\<lambda>f. image g o f) ` F) = image g o collect F"
by (rule ext) (auto simp add: collect_def)

lemma conj_subset_def: "A \<subseteq> {x. P x \<and> Q x} = (A \<subseteq> {x. P x} \<and> A \<subseteq> {x. Q x})"
by blast

lemma UN_image_subset: "\<Union>(f ` g x) \<subseteq> X = (g x \<subseteq> {x. f x \<subseteq> X})"
by blast

lemma comp_set_bd_Union_o_collect: "|\<Union>\<Union>((\<lambda>f. f x) ` X)| \<le>o hbd \<Longrightarrow> |(Union \<circ> collect X) x| \<le>o hbd"
by (unfold comp_apply collect_def SUP_def)

lemma wpull_cong:
"\<lbrakk>A' = A; B1' = B1; B2' = B2; wpull A B1 B2 f1 f2 p1 p2\<rbrakk> \<Longrightarrow> wpull A' B1' B2' f1 f2 p1 p2"
by simp

lemma Grp_fst_snd: "(Grp (Collect (split R)) fst)^--1 OO Grp (Collect (split R)) snd = R"
unfolding Grp_def fun_eq_iff relcompp.simps by auto

lemma OO_Grp_cong: "A = B \<Longrightarrow> (Grp A f)^--1 OO Grp A g = (Grp B f)^--1 OO Grp B g"
by (rule arg_cong)

lemma vimage2p_relcompp_mono: "R OO S \<le> T \<Longrightarrow>
  vimage2p f g R OO vimage2p g h S \<le> vimage2p f h T"
  unfolding vimage2p_def by auto

lemma type_copy_map_cong0: "M (g x) = N (h x) \<Longrightarrow> (f o M o g) x = (f o N o h) x"
  by auto

lemma type_copy_set_bd: "(\<And>y. |S y| \<le>o bd) \<Longrightarrow> |(S o Rep) x| \<le>o bd"
  by auto

lemma vimage2p_cong: "R = S \<Longrightarrow> vimage2p f g R = vimage2p f g S"
  by simp

context
fixes Rep Abs
assumes type_copy: "type_definition Rep Abs UNIV"
begin

lemma type_copy_map_id0: "M = id \<Longrightarrow> Abs o M o Rep = id"
  using type_definition.Rep_inverse[OF type_copy] by auto

lemma type_copy_map_comp0: "M = M1 o M2 \<Longrightarrow> f o M o g = (f o M1 o Rep) o (Abs o M2 o g)"
  using type_definition.Abs_inverse[OF type_copy UNIV_I] by auto

lemma type_copy_set_map0: "S o M = image f o S' \<Longrightarrow> (S o Rep) o (Abs o M o g) = image f o (S' o g)"
  using type_definition.Abs_inverse[OF type_copy UNIV_I] by (auto simp: o_def fun_eq_iff)

lemma type_copy_wit: "x \<in> (S o Rep) (Abs y) \<Longrightarrow> x \<in> S y"
  using type_definition.Abs_inverse[OF type_copy UNIV_I] by auto

lemma type_copy_vimage2p_Grp_Rep: "vimage2p f Rep (Grp (Collect P) h) =
    Grp (Collect (\<lambda>x. P (f x))) (Abs o h o f)"
  unfolding vimage2p_def Grp_def fun_eq_iff
  by (auto simp: type_definition.Abs_inverse[OF type_copy UNIV_I]
   type_definition.Rep_inverse[OF type_copy] dest: sym)

lemma type_copy_vimage2p_Grp_Abs:
  "\<And>h. vimage2p g Abs (Grp (Collect P) h) = Grp (Collect (\<lambda>x. P (g x))) (Rep o h o g)"
  unfolding vimage2p_def Grp_def fun_eq_iff
  by (auto simp: type_definition.Abs_inverse[OF type_copy UNIV_I]
   type_definition.Rep_inverse[OF type_copy] dest: sym)

lemma type_copy_ex_RepI: "(\<exists>b. F b) = (\<exists>b. F (Rep b))"
proof safe
  fix b assume "F b"
  show "\<exists>b'. F (Rep b')"
  proof (rule exI)
    from `F b` show "F (Rep (Abs b))" using type_definition.Abs_inverse[OF type_copy] by auto
  qed
qed blast

lemma vimage2p_relcompp_converse:
  "vimage2p f g (R^--1 OO S) = (vimage2p Rep f R)^--1 OO vimage2p Rep g S"
  unfolding vimage2p_def relcompp.simps conversep.simps fun_eq_iff image_def
  by (auto simp: type_copy_ex_RepI)

end

lemma csum_dup: "cinfinite r \<Longrightarrow> Card_order r \<Longrightarrow> p +c p' =o r +c r \<Longrightarrow> p +c p' =o r"
by (metis csum_absorb2' ordIso_transitive ordLeq_refl)

lemma cprod_dup: "cinfinite r \<Longrightarrow> Card_order r \<Longrightarrow> p *c p' =o r *c r \<Longrightarrow> p *c p' =o r"
by (metis cprod_infinite ordIso_transitive)

ML_file "Tools/BNF/bnf_comp_tactics.ML"
ML_file "Tools/BNF/bnf_comp.ML"

end
