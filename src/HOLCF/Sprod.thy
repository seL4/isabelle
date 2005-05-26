(*  Title:      HOLCF/Sprod.thy
    ID:         $Id$
    Author:     Franz Regensburger and Brian Huffman

Strict product with typedef.
*)

header {* The type of strict products *}

theory Sprod
imports Cprod TypedefPcpo
begin

defaultsort pcpo

subsection {* Definition of strict product type *}

typedef (Sprod)  ('a, 'b) "**" (infixr 20) =
        "{p::'a \<times> 'b. p = \<bottom> \<or> (cfst\<cdot>p \<noteq> \<bottom> \<and> csnd\<cdot>p \<noteq> \<bottom>)}"
by (auto simp add: inst_cprod_pcpo)

syntax (xsymbols)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)
syntax (HTML output)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)

subsection {* Class instances *}

instance "**" :: (pcpo, pcpo) sq_ord ..
defs (overloaded)
  less_sprod_def: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep_Sprod x \<sqsubseteq> Rep_Sprod y"

lemma adm_Sprod: "adm (\<lambda>x. x \<in> Sprod)"
by (simp add: Sprod_def)

lemma UU_Sprod: "\<bottom> \<in> Sprod"
by (simp add: Sprod_def)

instance "**" :: (pcpo, pcpo) po
by (rule typedef_po [OF type_definition_Sprod less_sprod_def])

instance "**" :: (pcpo, pcpo) cpo
by (rule typedef_cpo [OF type_definition_Sprod less_sprod_def adm_Sprod])

instance "**" :: (pcpo, pcpo) pcpo
by (rule typedef_pcpo_UU [OF type_definition_Sprod less_sprod_def UU_Sprod])

lemmas cont_Rep_Sprod =
  typedef_cont_Rep [OF type_definition_Sprod less_sprod_def adm_Sprod]

lemmas cont_Abs_Sprod = 
  typedef_cont_Abs [OF type_definition_Sprod less_sprod_def adm_Sprod]

lemmas strict_Rep_Sprod =
  typedef_strict_Rep [OF type_definition_Sprod less_sprod_def UU_Sprod]

lemmas strict_Abs_Sprod =
  typedef_strict_Abs [OF type_definition_Sprod less_sprod_def UU_Sprod]

lemma UU_Abs_Sprod: "\<bottom> = Abs_Sprod <\<bottom>, \<bottom>>"
by (simp add: strict_Abs_Sprod inst_cprod_pcpo2 [symmetric])

lemma spair_lemma:
  "<strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a> \<in> Sprod"
apply (simp add: Sprod_def inst_cprod_pcpo2)
apply (case_tac "a = \<bottom>", case_tac [!] "b = \<bottom>", simp_all)
done

subsection {* Definitions of constants *}

consts
  sfst :: "('a ** 'b) \<rightarrow> 'a"
  ssnd :: "('a ** 'b) \<rightarrow> 'b"
  spair :: "'a \<rightarrow> 'b \<rightarrow> ('a ** 'b)"
  ssplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a ** 'b) \<rightarrow> 'c"

defs
  sfst_def: "sfst \<equiv> \<Lambda> p. cfst\<cdot>(Rep_Sprod p)"
  ssnd_def: "ssnd \<equiv> \<Lambda> p. csnd\<cdot>(Rep_Sprod p)"
  spair_def: "spair \<equiv> \<Lambda> a b. Abs_Sprod
                <strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a>"
  ssplit_def: "ssplit \<equiv> \<Lambda> f. strictify\<cdot>(\<Lambda> p. f\<cdot>(sfst\<cdot>p)\<cdot>(ssnd\<cdot>p))"

syntax  
  "@stuple"	:: "['a, args] => 'a ** 'b"	("(1'(:_,/ _:'))")

translations
        "(:x, y, z:)"   == "(:x, (:y, z:):)"
        "(:x, y:)"      == "spair$x$y"

subsection {* Case analysis *}

lemma spair_Abs_Sprod:
  "(:a, b:) = Abs_Sprod <strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a>"
apply (unfold spair_def)
apply (simp add: cont_Abs_Sprod spair_lemma)
done

lemma Exh_Sprod2:
  "z = \<bottom> \<or> (\<exists>a b. z = (:a, b:) \<and> a \<noteq> \<bottom> \<and> b \<noteq> \<bottom>)"
apply (rule_tac x=z in Abs_Sprod_cases)
apply (simp add: Sprod_def)
apply (erule disjE)
apply (simp add: strict_Abs_Sprod)
apply (rule disjI2)
apply (rule_tac x="cfst\<cdot>y" in exI)
apply (rule_tac x="csnd\<cdot>y" in exI)
apply (simp add: spair_Abs_Sprod Abs_Sprod_inject spair_lemma)
apply (simp add: surjective_pairing_Cprod2)
done

lemma sprodE:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; \<And>x y. \<lbrakk>p = (:x, y:); x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cut_tac z=p in Exh_Sprod2, auto)

subsection {* Properties of @{term spair} *}

lemma strict_spair1 [simp]: "(:\<bottom>, b:) = \<bottom>"
apply (simp add: spair_Abs_Sprod UU_Abs_Sprod)
apply (case_tac "b = \<bottom>", simp_all)
done

lemma strict_spair2 [simp]: "(:a, \<bottom>:) = \<bottom>"
apply (simp add: spair_Abs_Sprod UU_Abs_Sprod)
apply (case_tac "a = \<bottom>", simp_all)
done

lemma strict_spair: "a = \<bottom> \<or> b = \<bottom> \<Longrightarrow> (:a, b:) = \<bottom>"
by auto

lemma strict_spair_rev: "(:x, y:) \<noteq> \<bottom> \<Longrightarrow> x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>"
by (erule contrapos_np, auto)

lemma defined_spair [simp]: 
  "\<lbrakk>a \<noteq> \<bottom>; b \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> (:a, b:) \<noteq> \<bottom>"
apply (simp add: spair_Abs_Sprod UU_Abs_Sprod)
apply (subst Abs_Sprod_inject)
apply (simp add: Sprod_def)
apply (simp add: Sprod_def inst_cprod_pcpo2)
apply simp
done

lemma defined_spair_rev: "(:a, b:) = \<bottom> \<Longrightarrow> a = \<bottom> \<or> b = \<bottom>"
by (erule contrapos_pp, simp)

lemma inject_spair: 
  "\<lbrakk>aa \<noteq> \<bottom>; ba \<noteq> \<bottom>; (:a,b:) = (:aa,ba:)\<rbrakk> \<Longrightarrow> a = aa \<and> b = ba"
apply (simp add: spair_Abs_Sprod)
apply (simp add: Abs_Sprod_inject [OF spair_lemma] Sprod_def)
apply (case_tac "a = \<bottom>", simp_all)
apply (case_tac "b = \<bottom>", simp_all)
done

lemma inst_sprod_pcpo2: "UU = (:UU,UU:)"
by simp

subsection {* Properties of @{term sfst} and @{term ssnd} *}

lemma strict_sfst [simp]: "sfst\<cdot>\<bottom> = \<bottom>"
by (simp add: sfst_def cont_Rep_Sprod strict_Rep_Sprod)

lemma strict_ssnd [simp]: "ssnd\<cdot>\<bottom> = \<bottom>"
by (simp add: ssnd_def cont_Rep_Sprod strict_Rep_Sprod)

lemma Rep_Sprod_spair:
  "Rep_Sprod (:a, b:) = <strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a>"
apply (unfold spair_def)
apply (simp add: cont_Abs_Sprod Abs_Sprod_inverse spair_lemma)
done

lemma sfst2 [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sfst\<cdot>(:x, y:) = x"
by (simp add: sfst_def cont_Rep_Sprod Rep_Sprod_spair)

lemma ssnd2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssnd\<cdot>(:x, y:) = y"
by (simp add: ssnd_def cont_Rep_Sprod Rep_Sprod_spair)

lemma defined_sfstssnd: "p \<noteq> \<bottom> \<Longrightarrow> sfst\<cdot>p \<noteq> \<bottom> \<and> ssnd\<cdot>p \<noteq> \<bottom>"
by (rule_tac p=p in sprodE, simp_all)
 
lemma surjective_pairing_Sprod2: "(:sfst\<cdot>p, ssnd\<cdot>p:) = p"
by (rule_tac p=p in sprodE, simp_all)

subsection {* Properties of @{term ssplit} *}

lemma ssplit1 [simp]: "ssplit\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (simp add: ssplit_def)

lemma ssplit2 [simp]: "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> ssplit\<cdot>f\<cdot>(:x, y:)= f\<cdot>x\<cdot>y"
by (simp add: ssplit_def)

lemma ssplit3: "ssplit\<cdot>spair\<cdot>z = z"
by (rule_tac p=z in sprodE, simp_all)

end
