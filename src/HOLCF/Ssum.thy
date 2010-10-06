(*  Title:      HOLCF/Ssum.thy
    Author:     Franz Regensburger and Brian Huffman
*)

header {* The type of strict sums *}

theory Ssum
imports Tr
begin

default_sort pcpo

subsection {* Definition of strict sum type *}

pcpodef (Ssum)  ('a, 'b) ssum (infixr "++" 10) = 
  "{p :: tr \<times> ('a \<times> 'b).
    (fst p \<sqsubseteq> TT \<longleftrightarrow> snd (snd p) = \<bottom>) \<and>
    (fst p \<sqsubseteq> FF \<longleftrightarrow> fst (snd p) = \<bottom>)}"
by simp_all

instance ssum :: ("{finite_po,pcpo}", "{finite_po,pcpo}") finite_po
by (rule typedef_finite_po [OF type_definition_Ssum])

instance ssum :: ("{chfin,pcpo}", "{chfin,pcpo}") chfin
by (rule typedef_chfin [OF type_definition_Ssum below_Ssum_def])

type_notation (xsymbols)
  ssum  ("(_ \<oplus>/ _)" [21, 20] 20)
type_notation (HTML output)
  ssum  ("(_ \<oplus>/ _)" [21, 20] 20)


subsection {* Definitions of constructors *}

definition
  sinl :: "'a \<rightarrow> ('a ++ 'b)" where
  "sinl = (\<Lambda> a. Abs_Ssum (strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>))"

definition
  sinr :: "'b \<rightarrow> ('a ++ 'b)" where
  "sinr = (\<Lambda> b. Abs_Ssum (strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b))"

lemma sinl_Ssum: "(strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>) \<in> Ssum"
by (simp add: Ssum_def strictify_conv_if)

lemma sinr_Ssum: "(strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b) \<in> Ssum"
by (simp add: Ssum_def strictify_conv_if)

lemma sinl_Abs_Ssum: "sinl\<cdot>a = Abs_Ssum (strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>)"
by (unfold sinl_def, simp add: cont_Abs_Ssum sinl_Ssum)

lemma sinr_Abs_Ssum: "sinr\<cdot>b = Abs_Ssum (strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b)"
by (unfold sinr_def, simp add: cont_Abs_Ssum sinr_Ssum)

lemma Rep_Ssum_sinl: "Rep_Ssum (sinl\<cdot>a) = (strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>)"
by (simp add: sinl_Abs_Ssum Abs_Ssum_inverse sinl_Ssum)

lemma Rep_Ssum_sinr: "Rep_Ssum (sinr\<cdot>b) = (strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b)"
by (simp add: sinr_Abs_Ssum Abs_Ssum_inverse sinr_Ssum)

subsection {* Properties of \emph{sinl} and \emph{sinr} *}

text {* Ordering *}

lemma sinl_below [simp]: "(sinl\<cdot>x \<sqsubseteq> sinl\<cdot>y) = (x \<sqsubseteq> y)"
by (simp add: below_Ssum_def Rep_Ssum_sinl strictify_conv_if)

lemma sinr_below [simp]: "(sinr\<cdot>x \<sqsubseteq> sinr\<cdot>y) = (x \<sqsubseteq> y)"
by (simp add: below_Ssum_def Rep_Ssum_sinr strictify_conv_if)

lemma sinl_below_sinr [simp]: "(sinl\<cdot>x \<sqsubseteq> sinr\<cdot>y) = (x = \<bottom>)"
by (simp add: below_Ssum_def Rep_Ssum_sinl Rep_Ssum_sinr strictify_conv_if)

lemma sinr_below_sinl [simp]: "(sinr\<cdot>x \<sqsubseteq> sinl\<cdot>y) = (x = \<bottom>)"
by (simp add: below_Ssum_def Rep_Ssum_sinl Rep_Ssum_sinr strictify_conv_if)

text {* Equality *}

lemma sinl_eq [simp]: "(sinl\<cdot>x = sinl\<cdot>y) = (x = y)"
by (simp add: po_eq_conv)

lemma sinr_eq [simp]: "(sinr\<cdot>x = sinr\<cdot>y) = (x = y)"
by (simp add: po_eq_conv)

lemma sinl_eq_sinr [simp]: "(sinl\<cdot>x = sinr\<cdot>y) = (x = \<bottom> \<and> y = \<bottom>)"
by (subst po_eq_conv, simp)

lemma sinr_eq_sinl [simp]: "(sinr\<cdot>x = sinl\<cdot>y) = (x = \<bottom> \<and> y = \<bottom>)"
by (subst po_eq_conv, simp)

lemma sinl_inject: "sinl\<cdot>x = sinl\<cdot>y \<Longrightarrow> x = y"
by (rule sinl_eq [THEN iffD1])

lemma sinr_inject: "sinr\<cdot>x = sinr\<cdot>y \<Longrightarrow> x = y"
by (rule sinr_eq [THEN iffD1])

text {* Strictness *}

lemma sinl_strict [simp]: "sinl\<cdot>\<bottom> = \<bottom>"
by (simp add: sinl_Abs_Ssum Abs_Ssum_strict)

lemma sinr_strict [simp]: "sinr\<cdot>\<bottom> = \<bottom>"
by (simp add: sinr_Abs_Ssum Abs_Ssum_strict)

lemma sinl_defined_iff [simp]: "(sinl\<cdot>x = \<bottom>) = (x = \<bottom>)"
by (cut_tac sinl_eq [of "x" "\<bottom>"], simp)

lemma sinr_defined_iff [simp]: "(sinr\<cdot>x = \<bottom>) = (x = \<bottom>)"
by (cut_tac sinr_eq [of "x" "\<bottom>"], simp)

lemma sinl_defined [intro!]: "x \<noteq> \<bottom> \<Longrightarrow> sinl\<cdot>x \<noteq> \<bottom>"
by simp

lemma sinr_defined [intro!]: "x \<noteq> \<bottom> \<Longrightarrow> sinr\<cdot>x \<noteq> \<bottom>"
by simp

text {* Compactness *}

lemma compact_sinl: "compact x \<Longrightarrow> compact (sinl\<cdot>x)"
by (rule compact_Ssum, simp add: Rep_Ssum_sinl strictify_conv_if)

lemma compact_sinr: "compact x \<Longrightarrow> compact (sinr\<cdot>x)"
by (rule compact_Ssum, simp add: Rep_Ssum_sinr strictify_conv_if)

lemma compact_sinlD: "compact (sinl\<cdot>x) \<Longrightarrow> compact x"
unfolding compact_def
by (drule adm_subst [OF cont_Rep_CFun2 [where f=sinl]], simp)

lemma compact_sinrD: "compact (sinr\<cdot>x) \<Longrightarrow> compact x"
unfolding compact_def
by (drule adm_subst [OF cont_Rep_CFun2 [where f=sinr]], simp)

lemma compact_sinl_iff [simp]: "compact (sinl\<cdot>x) = compact x"
by (safe elim!: compact_sinl compact_sinlD)

lemma compact_sinr_iff [simp]: "compact (sinr\<cdot>x) = compact x"
by (safe elim!: compact_sinr compact_sinrD)

subsection {* Case analysis *}

lemma Exh_Ssum: 
  "z = \<bottom> \<or> (\<exists>a. z = sinl\<cdot>a \<and> a \<noteq> \<bottom>) \<or> (\<exists>b. z = sinr\<cdot>b \<and> b \<noteq> \<bottom>)"
apply (induct z rule: Abs_Ssum_induct)
apply (case_tac y, rename_tac t a b)
apply (case_tac t rule: trE)
apply (rule disjI1)
apply (simp add: Ssum_def Abs_Ssum_strict)
apply (rule disjI2, rule disjI1, rule_tac x=a in exI)
apply (simp add: sinl_Abs_Ssum Ssum_def)
apply (rule disjI2, rule disjI2, rule_tac x=b in exI)
apply (simp add: sinr_Abs_Ssum Ssum_def)
done

lemma ssumE [case_names bottom sinl sinr, cases type: ssum]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q;
   \<And>x. \<lbrakk>p = sinl\<cdot>x; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q;
   \<And>y. \<lbrakk>p = sinr\<cdot>y; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
using Exh_Ssum [of p] by auto

lemma ssum_induct [case_names bottom sinl sinr, induct type: ssum]:
  "\<lbrakk>P \<bottom>;
   \<And>x. x \<noteq> \<bottom> \<Longrightarrow> P (sinl\<cdot>x);
   \<And>y. y \<noteq> \<bottom> \<Longrightarrow> P (sinr\<cdot>y)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

lemma ssumE2 [case_names sinl sinr]:
  "\<lbrakk>\<And>x. p = sinl\<cdot>x \<Longrightarrow> Q; \<And>y. p = sinr\<cdot>y \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cases p, simp only: sinl_strict [symmetric], simp, simp)

lemma below_sinlD: "p \<sqsubseteq> sinl\<cdot>x \<Longrightarrow> \<exists>y. p = sinl\<cdot>y \<and> y \<sqsubseteq> x"
by (cases p, rule_tac x="\<bottom>" in exI, simp_all)

lemma below_sinrD: "p \<sqsubseteq> sinr\<cdot>x \<Longrightarrow> \<exists>y. p = sinr\<cdot>y \<and> y \<sqsubseteq> x"
by (cases p, rule_tac x="\<bottom>" in exI, simp_all)

subsection {* Case analysis combinator *}

definition
  sscase :: "('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'c) \<rightarrow> ('a ++ 'b) \<rightarrow> 'c" where
  "sscase = (\<Lambda> f g s. (\<lambda>(t, x, y). If t then f\<cdot>x else g\<cdot>y fi) (Rep_Ssum s))"

translations
  "case s of XCONST sinl\<cdot>x \<Rightarrow> t1 | XCONST sinr\<cdot>y \<Rightarrow> t2" == "CONST sscase\<cdot>(\<Lambda> x. t1)\<cdot>(\<Lambda> y. t2)\<cdot>s"

translations
  "\<Lambda>(XCONST sinl\<cdot>x). t" == "CONST sscase\<cdot>(\<Lambda> x. t)\<cdot>\<bottom>"
  "\<Lambda>(XCONST sinr\<cdot>y). t" == "CONST sscase\<cdot>\<bottom>\<cdot>(\<Lambda> y. t)"

lemma beta_sscase:
  "sscase\<cdot>f\<cdot>g\<cdot>s = (\<lambda>(t, x, y). If t then f\<cdot>x else g\<cdot>y fi) (Rep_Ssum s)"
unfolding sscase_def by (simp add: cont_Rep_Ssum [THEN cont_compose])

lemma sscase1 [simp]: "sscase\<cdot>f\<cdot>g\<cdot>\<bottom> = \<bottom>"
unfolding beta_sscase by (simp add: Rep_Ssum_strict)

lemma sscase2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = f\<cdot>x"
unfolding beta_sscase by (simp add: Rep_Ssum_sinl)

lemma sscase3 [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>y) = g\<cdot>y"
unfolding beta_sscase by (simp add: Rep_Ssum_sinr)

lemma sscase4 [simp]: "sscase\<cdot>sinl\<cdot>sinr\<cdot>z = z"
by (cases z, simp_all)

subsection {* Strict sum preserves flatness *}

instance ssum :: (flat, flat) flat
apply (intro_classes, clarify)
apply (case_tac x, simp)
apply (case_tac y, simp_all add: flat_below_iff)
apply (case_tac y, simp_all add: flat_below_iff)
done

subsection {* Map function for strict sums *}

definition
  ssum_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<oplus> 'c \<rightarrow> 'b \<oplus> 'd"
where
  "ssum_map = (\<Lambda> f g. sscase\<cdot>(sinl oo f)\<cdot>(sinr oo g))"

lemma ssum_map_strict [simp]: "ssum_map\<cdot>f\<cdot>g\<cdot>\<bottom> = \<bottom>"
unfolding ssum_map_def by simp

lemma ssum_map_sinl [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = sinl\<cdot>(f\<cdot>x)"
unfolding ssum_map_def by simp

lemma ssum_map_sinr [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>x) = sinr\<cdot>(g\<cdot>x)"
unfolding ssum_map_def by simp

lemma ssum_map_sinl': "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = sinl\<cdot>(f\<cdot>x)"
by (cases "x = \<bottom>") simp_all

lemma ssum_map_sinr': "g\<cdot>\<bottom> = \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>x) = sinr\<cdot>(g\<cdot>x)"
by (cases "x = \<bottom>") simp_all

lemma ssum_map_ID: "ssum_map\<cdot>ID\<cdot>ID = ID"
unfolding ssum_map_def by (simp add: expand_cfun_eq eta_cfun)

lemma ssum_map_map:
  "\<lbrakk>f1\<cdot>\<bottom> = \<bottom>; g1\<cdot>\<bottom> = \<bottom>\<rbrakk> \<Longrightarrow>
    ssum_map\<cdot>f1\<cdot>g1\<cdot>(ssum_map\<cdot>f2\<cdot>g2\<cdot>p) =
     ssum_map\<cdot>(\<Lambda> x. f1\<cdot>(f2\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
apply (induct p, simp)
apply (case_tac "f2\<cdot>x = \<bottom>", simp, simp)
apply (case_tac "g2\<cdot>y = \<bottom>", simp, simp)
done

lemma ep_pair_ssum_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (ssum_map\<cdot>e1\<cdot>e2) (ssum_map\<cdot>p1\<cdot>p2)"
proof
  interpret e1p1: pcpo_ep_pair e1 p1 unfolding pcpo_ep_pair_def by fact
  interpret e2p2: pcpo_ep_pair e2 p2 unfolding pcpo_ep_pair_def by fact
  fix x show "ssum_map\<cdot>p1\<cdot>p2\<cdot>(ssum_map\<cdot>e1\<cdot>e2\<cdot>x) = x"
    by (induct x) simp_all
  fix y show "ssum_map\<cdot>e1\<cdot>e2\<cdot>(ssum_map\<cdot>p1\<cdot>p2\<cdot>y) \<sqsubseteq> y"
    apply (induct y, simp)
    apply (case_tac "p1\<cdot>x = \<bottom>", simp, simp add: e1p1.e_p_below)
    apply (case_tac "p2\<cdot>y = \<bottom>", simp, simp add: e2p2.e_p_below)
    done
qed

lemma deflation_ssum_map:
  assumes "deflation d1" and "deflation d2"
  shows "deflation (ssum_map\<cdot>d1\<cdot>d2)"
proof
  interpret d1: deflation d1 by fact
  interpret d2: deflation d2 by fact
  fix x
  show "ssum_map\<cdot>d1\<cdot>d2\<cdot>(ssum_map\<cdot>d1\<cdot>d2\<cdot>x) = ssum_map\<cdot>d1\<cdot>d2\<cdot>x"
    apply (induct x, simp)
    apply (case_tac "d1\<cdot>x = \<bottom>", simp, simp add: d1.idem)
    apply (case_tac "d2\<cdot>y = \<bottom>", simp, simp add: d2.idem)
    done
  show "ssum_map\<cdot>d1\<cdot>d2\<cdot>x \<sqsubseteq> x"
    apply (induct x, simp)
    apply (case_tac "d1\<cdot>x = \<bottom>", simp, simp add: d1.below)
    apply (case_tac "d2\<cdot>y = \<bottom>", simp, simp add: d2.below)
    done
qed

lemma finite_deflation_ssum_map:
  assumes "finite_deflation d1" and "finite_deflation d2"
  shows "finite_deflation (ssum_map\<cdot>d1\<cdot>d2)"
proof (rule finite_deflation_intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (ssum_map\<cdot>d1\<cdot>d2)" by (rule deflation_ssum_map)
  have "{x. ssum_map\<cdot>d1\<cdot>d2\<cdot>x = x} \<subseteq>
        (\<lambda>x. sinl\<cdot>x) ` {x. d1\<cdot>x = x} \<union>
        (\<lambda>x. sinr\<cdot>x) ` {x. d2\<cdot>x = x} \<union> {\<bottom>}"
    by (rule subsetI, case_tac x, simp_all)
  thus "finite {x. ssum_map\<cdot>d1\<cdot>d2\<cdot>x = x}"
    by (rule finite_subset, simp add: d1.finite_fixes d2.finite_fixes)
qed

subsection {* Strict sum is an SFP domain *}

definition
  ssum_approx :: "nat \<Rightarrow> udom \<oplus> udom \<rightarrow> udom \<oplus> udom"
where
  "ssum_approx = (\<lambda>i. ssum_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma ssum_approx: "approx_chain ssum_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. ssum_approx i)"
    unfolding ssum_approx_def by simp
  show "(\<Squnion>i. ssum_approx i) = ID"
    unfolding ssum_approx_def
    by (simp add: lub_distribs ssum_map_ID)
  show "\<And>i. finite_deflation (ssum_approx i)"
    unfolding ssum_approx_def
    by (intro finite_deflation_ssum_map finite_deflation_udom_approx)
qed

definition ssum_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "ssum_sfp = sfp_fun2 ssum_approx ssum_map"

lemma cast_ssum_sfp:
  "cast\<cdot>(ssum_sfp\<cdot>A\<cdot>B) =
    udom_emb ssum_approx oo ssum_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj ssum_approx"
unfolding ssum_sfp_def
apply (rule cast_sfp_fun2 [OF ssum_approx])
apply (erule (1) finite_deflation_ssum_map)
done

instantiation ssum :: (sfp, sfp) sfp
begin

definition
  "emb = udom_emb ssum_approx oo ssum_map\<cdot>emb\<cdot>emb"

definition
  "prj = ssum_map\<cdot>prj\<cdot>prj oo udom_prj ssum_approx"

definition
  "sfp (t::('a \<oplus> 'b) itself) = ssum_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def
    using ep_pair_udom [OF ssum_approx]
    by (intro ep_pair_comp ep_pair_ssum_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<oplus> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<oplus> 'b)"
    unfolding emb_ssum_def prj_ssum_def sfp_ssum_def cast_ssum_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq ssum_map_map)
qed

end

text {* SFP of type constructor = type combinator *}

lemma SFP_ssum: "SFP('a::sfp \<oplus> 'b::sfp) = ssum_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_ssum_def)

end
