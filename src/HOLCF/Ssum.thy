(*  Title:      HOLCF/Ssum.thy
    Author:     Franz Regensburger and Brian Huffman
*)

header {* The type of strict sums *}

theory Ssum
imports Cprod Tr
begin

defaultsort pcpo

subsection {* Definition of strict sum type *}

pcpodef (Ssum)  ('a, 'b) "++" (infixr "++" 10) = 
  "{p :: tr \<times> ('a \<times> 'b).
    (cfst\<cdot>p \<sqsubseteq> TT \<longleftrightarrow> csnd\<cdot>(csnd\<cdot>p) = \<bottom>) \<and>
    (cfst\<cdot>p \<sqsubseteq> FF \<longleftrightarrow> cfst\<cdot>(csnd\<cdot>p) = \<bottom>)}"
by simp_all

instance "++" :: ("{finite_po,pcpo}", "{finite_po,pcpo}") finite_po
by (rule typedef_finite_po [OF type_definition_Ssum])

instance "++" :: ("{chfin,pcpo}", "{chfin,pcpo}") chfin
by (rule typedef_chfin [OF type_definition_Ssum below_Ssum_def])

syntax (xsymbols)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)
syntax (HTML output)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)

subsection {* Definitions of constructors *}

definition
  sinl :: "'a \<rightarrow> ('a ++ 'b)" where
  "sinl = (\<Lambda> a. Abs_Ssum <strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>>)"

definition
  sinr :: "'b \<rightarrow> ('a ++ 'b)" where
  "sinr = (\<Lambda> b. Abs_Ssum <strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b>)"

lemma sinl_Ssum: "<strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>> \<in> Ssum"
by (simp add: Ssum_def strictify_conv_if)

lemma sinr_Ssum: "<strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b> \<in> Ssum"
by (simp add: Ssum_def strictify_conv_if)

lemma sinl_Abs_Ssum: "sinl\<cdot>a = Abs_Ssum <strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>>"
by (unfold sinl_def, simp add: cont_Abs_Ssum sinl_Ssum)

lemma sinr_Abs_Ssum: "sinr\<cdot>b = Abs_Ssum <strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b>"
by (unfold sinr_def, simp add: cont_Abs_Ssum sinr_Ssum)

lemma Rep_Ssum_sinl: "Rep_Ssum (sinl\<cdot>a) = <strictify\<cdot>(\<Lambda> _. TT)\<cdot>a, a, \<bottom>>"
by (simp add: sinl_Abs_Ssum Abs_Ssum_inverse sinl_Ssum)

lemma Rep_Ssum_sinr: "Rep_Ssum (sinr\<cdot>b) = <strictify\<cdot>(\<Lambda> _. FF)\<cdot>b, \<bottom>, b>"
by (simp add: sinr_Abs_Ssum Abs_Ssum_inverse sinr_Ssum)

subsection {* Properties of @{term sinl} and @{term sinr} *}

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
apply (rule_tac x=z in Abs_Ssum_induct)
apply (rule_tac p=y in cprodE, rename_tac t x)
apply (rule_tac p=x in cprodE, rename_tac a b)
apply (rule_tac p=t in trE)
apply (rule disjI1)
apply (simp add: Ssum_def cpair_strict Abs_Ssum_strict)
apply (rule disjI2, rule disjI1, rule_tac x=a in exI)
apply (simp add: sinl_Abs_Ssum Ssum_def)
apply (rule disjI2, rule disjI2, rule_tac x=b in exI)
apply (simp add: sinr_Abs_Ssum Ssum_def)
done

lemma ssumE [cases type: ++]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q;
   \<And>x. \<lbrakk>p = sinl\<cdot>x; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q;
   \<And>y. \<lbrakk>p = sinr\<cdot>y; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cut_tac z=p in Exh_Ssum, auto)

lemma ssum_induct [induct type: ++]:
  "\<lbrakk>P \<bottom>;
   \<And>x. x \<noteq> \<bottom> \<Longrightarrow> P (sinl\<cdot>x);
   \<And>y. y \<noteq> \<bottom> \<Longrightarrow> P (sinr\<cdot>y)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

lemma ssumE2:
  "\<lbrakk>\<And>x. p = sinl\<cdot>x \<Longrightarrow> Q; \<And>y. p = sinr\<cdot>y \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cases p, simp only: sinl_strict [symmetric], simp, simp)

lemma below_sinlD: "p \<sqsubseteq> sinl\<cdot>x \<Longrightarrow> \<exists>y. p = sinl\<cdot>y \<and> y \<sqsubseteq> x"
by (cases p, rule_tac x="\<bottom>" in exI, simp_all)

lemma below_sinrD: "p \<sqsubseteq> sinr\<cdot>x \<Longrightarrow> \<exists>y. p = sinr\<cdot>y \<and> y \<sqsubseteq> x"
by (cases p, rule_tac x="\<bottom>" in exI, simp_all)

subsection {* Case analysis combinator *}

definition
  sscase :: "('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'c) \<rightarrow> ('a ++ 'b) \<rightarrow> 'c" where
  "sscase = (\<Lambda> f g s. (\<Lambda><t, x, y>. If t then f\<cdot>x else g\<cdot>y fi)\<cdot>(Rep_Ssum s))"

translations
  "case s of XCONST sinl\<cdot>x \<Rightarrow> t1 | XCONST sinr\<cdot>y \<Rightarrow> t2" == "CONST sscase\<cdot>(\<Lambda> x. t1)\<cdot>(\<Lambda> y. t2)\<cdot>s"

translations
  "\<Lambda>(XCONST sinl\<cdot>x). t" == "CONST sscase\<cdot>(\<Lambda> x. t)\<cdot>\<bottom>"
  "\<Lambda>(XCONST sinr\<cdot>y). t" == "CONST sscase\<cdot>\<bottom>\<cdot>(\<Lambda> y. t)"

lemma beta_sscase:
  "sscase\<cdot>f\<cdot>g\<cdot>s = (\<Lambda><t, x, y>. If t then f\<cdot>x else g\<cdot>y fi)\<cdot>(Rep_Ssum s)"
unfolding sscase_def by (simp add: cont_Rep_Ssum cont2cont_LAM)

lemma sscase1 [simp]: "sscase\<cdot>f\<cdot>g\<cdot>\<bottom> = \<bottom>"
unfolding beta_sscase by (simp add: Rep_Ssum_strict)

lemma sscase2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = f\<cdot>x"
unfolding beta_sscase by (simp add: Rep_Ssum_sinl)

lemma sscase3 [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>y) = g\<cdot>y"
unfolding beta_sscase by (simp add: Rep_Ssum_sinr)

lemma sscase4 [simp]: "sscase\<cdot>sinl\<cdot>sinr\<cdot>z = z"
by (cases z, simp_all)

subsection {* Strict sum preserves flatness *}

instance "++" :: (flat, flat) flat
apply (intro_classes, clarify)
apply (rule_tac p=x in ssumE, simp)
apply (rule_tac p=y in ssumE, simp_all add: flat_below_iff)
apply (rule_tac p=y in ssumE, simp_all add: flat_below_iff)
done

subsection {* Strict sum is a bifinite domain *}

instantiation "++" :: (bifinite, bifinite) bifinite
begin

definition
  approx_ssum_def:
    "approx = (\<lambda>n. sscase\<cdot>(\<Lambda> x. sinl\<cdot>(approx n\<cdot>x))\<cdot>(\<Lambda> y. sinr\<cdot>(approx n\<cdot>y)))"

lemma approx_sinl [simp]: "approx i\<cdot>(sinl\<cdot>x) = sinl\<cdot>(approx i\<cdot>x)"
unfolding approx_ssum_def by (cases "x = \<bottom>") simp_all

lemma approx_sinr [simp]: "approx i\<cdot>(sinr\<cdot>x) = sinr\<cdot>(approx i\<cdot>x)"
unfolding approx_ssum_def by (cases "x = \<bottom>") simp_all

instance proof
  fix i :: nat and x :: "'a \<oplus> 'b"
  show "chain (approx :: nat \<Rightarrow> 'a \<oplus> 'b \<rightarrow> 'a \<oplus> 'b)"
    unfolding approx_ssum_def by simp
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx_ssum_def
    by (simp add: lub_distribs eta_cfun)
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    by (cases x, simp add: approx_ssum_def, simp, simp)
  have "{x::'a \<oplus> 'b. approx i\<cdot>x = x} \<subseteq>
        (\<lambda>x. sinl\<cdot>x) ` {x. approx i\<cdot>x = x} \<union>
        (\<lambda>x. sinr\<cdot>x) ` {x. approx i\<cdot>x = x}"
    by (rule subsetI, case_tac x rule: ssumE2, simp, simp)
  thus "finite {x::'a \<oplus> 'b. approx i\<cdot>x = x}"
    by (rule finite_subset,
        intro finite_UnI finite_imageI finite_fixes_approx)
qed

end

end
