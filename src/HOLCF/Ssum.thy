(*  Title:      HOLCF/Ssum.thy
    ID:         $Id$
    Author:     Franz Regensburger and Brian Huffman

Strict sum with typedef.
*)

header {* The type of strict sums *}

theory Ssum
imports Cprod TypedefPcpo
begin

defaultsort pcpo

subsection {* Definition of strict sum type *}

typedef (Ssum)  ('a, 'b) "++" (infixr 10) = 
        "{p::'a \<times> 'b. cfst\<cdot>p = \<bottom> \<or> csnd\<cdot>p = \<bottom>}"
by (rule_tac x="<\<bottom>,\<bottom>>" in exI, simp)

syntax (xsymbols)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)
syntax (HTML output)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)

subsection {* Class instances *}

instance "++" :: (pcpo, pcpo) sq_ord ..
defs (overloaded)
  less_ssum_def: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep_Ssum x \<sqsubseteq> Rep_Ssum y"

lemma adm_Ssum: "adm (\<lambda>x. x \<in> Ssum)"
by (simp add: Ssum_def cont_fst cont_snd)

lemma UU_Ssum: "\<bottom> \<in> Ssum"
by (simp add: Ssum_def inst_cprod_pcpo2)

instance "++" :: (pcpo, pcpo) po
by (rule typedef_po [OF type_definition_Ssum less_ssum_def])

instance "++" :: (pcpo, pcpo) cpo
by (rule typedef_cpo [OF type_definition_Ssum less_ssum_def adm_Ssum])

instance "++" :: (pcpo, pcpo) pcpo
by (rule typedef_pcpo_UU [OF type_definition_Ssum less_ssum_def UU_Ssum])

lemmas cont_Rep_Ssum =
  typedef_cont_Rep [OF type_definition_Ssum less_ssum_def adm_Ssum]

lemmas cont_Abs_Ssum = 
  typedef_cont_Abs [OF type_definition_Ssum less_ssum_def adm_Ssum]

lemmas Rep_Ssum_strict =
  typedef_Rep_strict [OF type_definition_Ssum less_ssum_def UU_Ssum]

lemmas Abs_Ssum_strict =
  typedef_Abs_strict [OF type_definition_Ssum less_ssum_def UU_Ssum]

lemma UU_Abs_Ssum: "\<bottom> = Abs_Ssum <\<bottom>, \<bottom>>"
by (simp add: Abs_Ssum_strict inst_cprod_pcpo2 [symmetric])


subsection {* Definitions of constructors *}

constdefs
  sinl :: "'a \<rightarrow> ('a ++ 'b)"
  "sinl \<equiv> \<Lambda> a. Abs_Ssum <a, \<bottom>>"

  sinr :: "'b \<rightarrow> ('a ++ 'b)"
  "sinr \<equiv> \<Lambda> b. Abs_Ssum <\<bottom>, b>"

subsection {* Properties of @{term sinl} and @{term sinr} *}

lemma sinl_Abs_Ssum: "sinl\<cdot>a = Abs_Ssum <a, \<bottom>>"
by (unfold sinl_def, simp add: cont_Abs_Ssum Ssum_def)

lemma sinr_Abs_Ssum: "sinr\<cdot>b = Abs_Ssum <\<bottom>, b>"
by (unfold sinr_def, simp add: cont_Abs_Ssum Ssum_def)

lemma Rep_Ssum_sinl: "Rep_Ssum (sinl\<cdot>a) = <a, \<bottom>>"
by (unfold sinl_def, simp add: cont_Abs_Ssum Abs_Ssum_inverse Ssum_def)

lemma Rep_Ssum_sinr: "Rep_Ssum (sinr\<cdot>b) = <\<bottom>, b>"
by (unfold sinr_def, simp add: cont_Abs_Ssum Abs_Ssum_inverse Ssum_def)

lemma sinl_strict [simp]: "sinl\<cdot>\<bottom> = \<bottom>"
by (simp add: sinl_Abs_Ssum UU_Abs_Ssum)

lemma sinr_strict [simp]: "sinr\<cdot>\<bottom> = \<bottom>"
by (simp add: sinr_Abs_Ssum UU_Abs_Ssum)

lemma noteq_sinlsinr: "sinl\<cdot>a = sinr\<cdot>b \<Longrightarrow> a = \<bottom> \<and> b = \<bottom>"
apply (simp add: sinl_Abs_Ssum sinr_Abs_Ssum)
apply (simp add: Abs_Ssum_inject Ssum_def)
done

lemma sinl_inject: "sinl\<cdot>x = sinl\<cdot>y \<Longrightarrow> x = y"
by (simp add: sinl_Abs_Ssum Abs_Ssum_inject Ssum_def)

lemma sinr_inject: "sinr\<cdot>x = sinr\<cdot>y \<Longrightarrow> x = y"
by (simp add: sinr_Abs_Ssum Abs_Ssum_inject Ssum_def)

lemma sinl_eq: "(sinl\<cdot>x = sinl\<cdot>y) = (x = y)"
by (simp add: sinl_Abs_Ssum Abs_Ssum_inject Ssum_def)

lemma sinr_eq: "(sinr\<cdot>x = sinr\<cdot>y) = (x = y)"
by (simp add: sinr_Abs_Ssum Abs_Ssum_inject Ssum_def)

lemma sinl_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> sinl\<cdot>x \<noteq> \<bottom>"
apply (erule contrapos_nn)
apply (rule sinl_inject)
apply auto
done

lemma sinr_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> sinr\<cdot>x \<noteq> \<bottom>"
apply (erule contrapos_nn)
apply (rule sinr_inject)
apply auto
done

subsection {* Case analysis *}

lemma Exh_Ssum1: 
  "z = \<bottom> \<or> (\<exists>a. z = sinl\<cdot>a \<and> a \<noteq> \<bottom>) \<or> (\<exists>b. z = sinr\<cdot>b \<and> b \<noteq> \<bottom>)"
apply (simp add: sinl_Abs_Ssum sinr_Abs_Ssum UU_Abs_Ssum)
apply (rule_tac x=z in Abs_Ssum_cases)
apply (rule_tac p=y in cprodE)
apply (auto simp add: Ssum_def)
done

lemma ssumE:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q;
   \<And>x. \<lbrakk>p = sinl\<cdot>x; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q;
   \<And>y. \<lbrakk>p = sinr\<cdot>y; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cut_tac z=p in Exh_Ssum1, auto)

lemma ssumE2:
  "\<lbrakk>\<And>x. p = sinl\<cdot>x \<Longrightarrow> Q; \<And>y. p = sinr\<cdot>y \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (rule_tac p=p in ssumE)
apply (simp only: sinl_strict [symmetric])
apply simp
apply simp
done

subsection {* Ordering properties of @{term sinl} and @{term sinr} *}

lemma less_ssum4a: "(sinl\<cdot>x \<sqsubseteq> sinl\<cdot>y) = (x \<sqsubseteq> y)"
by (simp add: less_ssum_def Rep_Ssum_sinl cpair_less)

lemma less_ssum4b: "(sinr\<cdot>x \<sqsubseteq> sinr\<cdot>y) = (x \<sqsubseteq> y)"
by (simp add: less_ssum_def Rep_Ssum_sinr cpair_less)

lemma less_ssum4c: "(sinl\<cdot>x \<sqsubseteq> sinr\<cdot>y) = (x = \<bottom>)"
by (simp add: less_ssum_def Rep_Ssum_sinl Rep_Ssum_sinr cpair_less eq_UU_iff)

lemma less_ssum4d: "(sinr\<cdot>x \<sqsubseteq> sinl\<cdot>y) = (x = \<bottom>)"
by (simp add: less_ssum_def Rep_Ssum_sinl Rep_Ssum_sinr cpair_less eq_UU_iff)

subsection {* Chains of strict sums *}

lemma less_sinlD: "p \<sqsubseteq> sinl\<cdot>x \<Longrightarrow> \<exists>y. p = sinl\<cdot>y \<and> y \<sqsubseteq> x"
apply (rule_tac p=p in ssumE)
apply (rule_tac x="\<bottom>" in exI, simp)
apply (simp add: less_ssum4a sinl_eq)
apply (simp add: less_ssum4d)
done

lemma less_sinrD: "p \<sqsubseteq> sinr\<cdot>x \<Longrightarrow> \<exists>y. p = sinr\<cdot>y \<and> y \<sqsubseteq> x"
apply (rule_tac p=p in ssumE)
apply (rule_tac x="\<bottom>" in exI, simp)
apply (simp add: less_ssum4c)
apply (simp add: less_ssum4b sinr_eq)
done

lemma ssum_chain_lemma:
"chain Y \<Longrightarrow> (\<exists>A. chain A \<and> Y = (\<lambda>i. sinl\<cdot>(A i))) \<or>
             (\<exists>B. chain B \<and> Y = (\<lambda>i. sinr\<cdot>(B i)))"
 apply (rule_tac p="lub (range Y)" in ssumE2)
  apply (rule disjI1)
  apply (rule_tac x="\<lambda>i. cfst\<cdot>(Rep_Ssum (Y i))" in exI)
  apply (rule conjI)
   apply (rule chain_monofun)
   apply (erule cont_Rep_Ssum [THEN cont2mono, THEN ch2ch_monofun])
  apply (rule ext, drule_tac x=i in is_ub_thelub, simp)
  apply (drule less_sinlD, clarify)
  apply (simp add: sinl_eq Rep_Ssum_sinl)
 apply (rule disjI2)
 apply (rule_tac x="\<lambda>i. csnd\<cdot>(Rep_Ssum (Y i))" in exI)
 apply (rule conjI)
  apply (rule chain_monofun)
  apply (erule cont_Rep_Ssum [THEN cont2mono, THEN ch2ch_monofun])
 apply (rule ext, drule_tac x=i in is_ub_thelub, simp)
 apply (drule less_sinrD, clarify)
 apply (simp add: sinr_eq Rep_Ssum_sinr)
done

subsection {* Definitions of constants *}

constdefs
  Iwhen :: "['a \<rightarrow> 'c, 'b \<rightarrow> 'c, 'a ++ 'b] \<Rightarrow> 'c"
  "Iwhen \<equiv> \<lambda>f g s.
    if cfst\<cdot>(Rep_Ssum s) \<noteq> \<bottom> then f\<cdot>(cfst\<cdot>(Rep_Ssum s)) else
    if csnd\<cdot>(Rep_Ssum s) \<noteq> \<bottom> then g\<cdot>(csnd\<cdot>(Rep_Ssum s)) else \<bottom>"

text {* rewrites for @{term Iwhen} *}

lemma Iwhen1 [simp]: "Iwhen f g \<bottom> = \<bottom>"
by (simp add: Iwhen_def Rep_Ssum_strict)

lemma Iwhen2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> Iwhen f g (sinl\<cdot>x) = f\<cdot>x"
by (simp add: Iwhen_def Rep_Ssum_sinl)

lemma Iwhen3 [simp]: "y \<noteq> \<bottom> \<Longrightarrow> Iwhen f g (sinr\<cdot>y) = g\<cdot>y"
by (simp add: Iwhen_def Rep_Ssum_sinr)

lemma Iwhen4: "Iwhen f g (sinl\<cdot>x) = strictify\<cdot>f\<cdot>x"
by (simp add: strictify_conv_if)

lemma Iwhen5: "Iwhen f g (sinr\<cdot>y) = strictify\<cdot>g\<cdot>y"
by (simp add: strictify_conv_if)

subsection {* Continuity of @{term Iwhen} *}

text {* @{term Iwhen} is continuous in all arguments *}

lemma cont_Iwhen1: "cont (\<lambda>f. Iwhen f g s)"
by (rule_tac p=s in ssumE, simp_all)

lemma cont_Iwhen2: "cont (\<lambda>g. Iwhen f g s)"
by (rule_tac p=s in ssumE, simp_all)

lemma cont_Iwhen3: "cont (\<lambda>s. Iwhen f g s)"
apply (rule contI)
apply (drule ssum_chain_lemma, safe)
apply (simp add: contlub_cfun_arg [symmetric])
apply (simp add: Iwhen4)
apply (simp add: contlub_cfun_arg)
apply (simp add: thelubE chain_monofun)
apply (simp add: contlub_cfun_arg [symmetric])
apply (simp add: Iwhen5)
apply (simp add: contlub_cfun_arg)
apply (simp add: thelubE chain_monofun)
done

subsection {* Continuous versions of constants *}

constdefs
  sscase :: "('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'c) \<rightarrow> ('a ++ 'b) \<rightarrow> 'c"
  "sscase \<equiv> \<Lambda> f g s. Iwhen f g s"

translations
"case s of sinl$x => t1 | sinr$y => t2" == "sscase$(LAM x. t1)$(LAM y. t2)$s"

text {* continuous versions of lemmas for @{term sscase} *}

lemma beta_sscase: "sscase\<cdot>f\<cdot>g\<cdot>s = Iwhen f g s"
by (simp add: sscase_def cont_Iwhen1 cont_Iwhen2 cont_Iwhen3)

lemma sscase1 [simp]: "sscase\<cdot>f\<cdot>g\<cdot>\<bottom> = \<bottom>"
by (simp add: beta_sscase)

lemma sscase2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = f\<cdot>x"
by (simp add: beta_sscase)

lemma sscase3 [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sscase\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>y) = g\<cdot>y"
by (simp add: beta_sscase)

lemma sscase4 [simp]: "sscase\<cdot>sinl\<cdot>sinr\<cdot>z = z"
by (rule_tac p=z in ssumE, simp_all)

end
