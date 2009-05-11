(*  Title:      HOLCF/Sprod.thy
    Author:     Franz Regensburger and Brian Huffman
*)

header {* The type of strict products *}

theory Sprod
imports Cprod
begin

defaultsort pcpo

subsection {* Definition of strict product type *}

pcpodef (Sprod)  ('a, 'b) "**" (infixr "**" 20) =
        "{p::'a \<times> 'b. p = \<bottom> \<or> (cfst\<cdot>p \<noteq> \<bottom> \<and> csnd\<cdot>p \<noteq> \<bottom>)}"
by simp_all

instance "**" :: ("{finite_po,pcpo}", "{finite_po,pcpo}") finite_po
by (rule typedef_finite_po [OF type_definition_Sprod])

instance "**" :: ("{chfin,pcpo}", "{chfin,pcpo}") chfin
by (rule typedef_chfin [OF type_definition_Sprod below_Sprod_def])

syntax (xsymbols)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)
syntax (HTML output)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)

lemma spair_lemma:
  "<strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a> \<in> Sprod"
by (simp add: Sprod_def strictify_conv_if)

subsection {* Definitions of constants *}

definition
  sfst :: "('a ** 'b) \<rightarrow> 'a" where
  "sfst = (\<Lambda> p. cfst\<cdot>(Rep_Sprod p))"

definition
  ssnd :: "('a ** 'b) \<rightarrow> 'b" where
  "ssnd = (\<Lambda> p. csnd\<cdot>(Rep_Sprod p))"

definition
  spair :: "'a \<rightarrow> 'b \<rightarrow> ('a ** 'b)" where
  "spair = (\<Lambda> a b. Abs_Sprod
             <strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a>)"

definition
  ssplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a ** 'b) \<rightarrow> 'c" where
  "ssplit = (\<Lambda> f. strictify\<cdot>(\<Lambda> p. f\<cdot>(sfst\<cdot>p)\<cdot>(ssnd\<cdot>p)))"

syntax
  "@stuple" :: "['a, args] => 'a ** 'b"  ("(1'(:_,/ _:'))")
translations
  "(:x, y, z:)" == "(:x, (:y, z:):)"
  "(:x, y:)"    == "CONST spair\<cdot>x\<cdot>y"

translations
  "\<Lambda>(CONST spair\<cdot>x\<cdot>y). t" == "CONST ssplit\<cdot>(\<Lambda> x y. t)"

subsection {* Case analysis *}

lemma Rep_Sprod_spair:
  "Rep_Sprod (:a, b:) = <strictify\<cdot>(\<Lambda> b. a)\<cdot>b, strictify\<cdot>(\<Lambda> a. b)\<cdot>a>"
unfolding spair_def
by (simp add: cont_Abs_Sprod Abs_Sprod_inverse spair_lemma)

lemmas Rep_Sprod_simps =
  Rep_Sprod_inject [symmetric] below_Sprod_def
  Rep_Sprod_strict Rep_Sprod_spair

lemma Exh_Sprod:
  "z = \<bottom> \<or> (\<exists>a b. z = (:a, b:) \<and> a \<noteq> \<bottom> \<and> b \<noteq> \<bottom>)"
apply (insert Rep_Sprod [of z])
apply (simp add: Rep_Sprod_simps eq_cprod)
apply (simp add: Sprod_def)
apply (erule disjE, simp)
apply (simp add: strictify_conv_if)
apply fast
done

lemma sprodE [cases type: **]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; \<And>x y. \<lbrakk>p = (:x, y:); x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cut_tac z=p in Exh_Sprod, auto)

lemma sprod_induct [induct type: **]:
  "\<lbrakk>P \<bottom>; \<And>x y. \<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> P (:x, y:)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

subsection {* Properties of @{term spair} *}

lemma spair_strict1 [simp]: "(:\<bottom>, y:) = \<bottom>"
by (simp add: Rep_Sprod_simps strictify_conv_if)

lemma spair_strict2 [simp]: "(:x, \<bottom>:) = \<bottom>"
by (simp add: Rep_Sprod_simps strictify_conv_if)

lemma spair_strict_iff [simp]: "((:x, y:) = \<bottom>) = (x = \<bottom> \<or> y = \<bottom>)"
by (simp add: Rep_Sprod_simps strictify_conv_if)

lemma spair_below_iff:
  "((:a, b:) \<sqsubseteq> (:c, d:)) = (a = \<bottom> \<or> b = \<bottom> \<or> (a \<sqsubseteq> c \<and> b \<sqsubseteq> d))"
by (simp add: Rep_Sprod_simps strictify_conv_if)

lemma spair_eq_iff:
  "((:a, b:) = (:c, d:)) =
    (a = c \<and> b = d \<or> (a = \<bottom> \<or> b = \<bottom>) \<and> (c = \<bottom> \<or> d = \<bottom>))"
by (simp add: Rep_Sprod_simps strictify_conv_if)

lemma spair_strict: "x = \<bottom> \<or> y = \<bottom> \<Longrightarrow> (:x, y:) = \<bottom>"
by simp

lemma spair_strict_rev: "(:x, y:) \<noteq> \<bottom> \<Longrightarrow> x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>"
by simp

lemma spair_defined: "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> (:x, y:) \<noteq> \<bottom>"
by simp

lemma spair_defined_rev: "(:x, y:) = \<bottom> \<Longrightarrow> x = \<bottom> \<or> y = \<bottom>"
by simp

lemma spair_eq:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> ((:x, y:) = (:a, b:)) = (x = a \<and> y = b)"
by (simp add: spair_eq_iff)

lemma spair_inject:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>; (:x, y:) = (:a, b:)\<rbrakk> \<Longrightarrow> x = a \<and> y = b"
by (rule spair_eq [THEN iffD1])

lemma inst_sprod_pcpo2: "UU = (:UU,UU:)"
by simp

subsection {* Properties of @{term sfst} and @{term ssnd} *}

lemma sfst_strict [simp]: "sfst\<cdot>\<bottom> = \<bottom>"
by (simp add: sfst_def cont_Rep_Sprod Rep_Sprod_strict)

lemma ssnd_strict [simp]: "ssnd\<cdot>\<bottom> = \<bottom>"
by (simp add: ssnd_def cont_Rep_Sprod Rep_Sprod_strict)

lemma sfst_spair [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sfst\<cdot>(:x, y:) = x"
by (simp add: sfst_def cont_Rep_Sprod Rep_Sprod_spair)

lemma ssnd_spair [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssnd\<cdot>(:x, y:) = y"
by (simp add: ssnd_def cont_Rep_Sprod Rep_Sprod_spair)

lemma sfst_defined_iff [simp]: "(sfst\<cdot>p = \<bottom>) = (p = \<bottom>)"
by (cases p, simp_all)

lemma ssnd_defined_iff [simp]: "(ssnd\<cdot>p = \<bottom>) = (p = \<bottom>)"
by (cases p, simp_all)

lemma sfst_defined: "p \<noteq> \<bottom> \<Longrightarrow> sfst\<cdot>p \<noteq> \<bottom>"
by simp

lemma ssnd_defined: "p \<noteq> \<bottom> \<Longrightarrow> ssnd\<cdot>p \<noteq> \<bottom>"
by simp

lemma surjective_pairing_Sprod2: "(:sfst\<cdot>p, ssnd\<cdot>p:) = p"
by (cases p, simp_all)

lemma below_sprod: "x \<sqsubseteq> y = (sfst\<cdot>x \<sqsubseteq> sfst\<cdot>y \<and> ssnd\<cdot>x \<sqsubseteq> ssnd\<cdot>y)"
apply (simp add: below_Sprod_def sfst_def ssnd_def cont_Rep_Sprod)
apply (rule below_cprod)
done

lemma eq_sprod: "(x = y) = (sfst\<cdot>x = sfst\<cdot>y \<and> ssnd\<cdot>x = ssnd\<cdot>y)"
by (auto simp add: po_eq_conv below_sprod)

lemma spair_below:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> (:x, y:) \<sqsubseteq> (:a, b:) = (x \<sqsubseteq> a \<and> y \<sqsubseteq> b)"
apply (cases "a = \<bottom>", simp)
apply (cases "b = \<bottom>", simp)
apply (simp add: below_sprod)
done

lemma sfst_below_iff: "sfst\<cdot>x \<sqsubseteq> y = x \<sqsubseteq> (:y, ssnd\<cdot>x:)"
apply (cases "x = \<bottom>", simp, cases "y = \<bottom>", simp)
apply (simp add: below_sprod)
done

lemma ssnd_below_iff: "ssnd\<cdot>x \<sqsubseteq> y = x \<sqsubseteq> (:sfst\<cdot>x, y:)"
apply (cases "x = \<bottom>", simp, cases "y = \<bottom>", simp)
apply (simp add: below_sprod)
done

subsection {* Compactness *}

lemma compact_sfst: "compact x \<Longrightarrow> compact (sfst\<cdot>x)"
by (rule compactI, simp add: sfst_below_iff)

lemma compact_ssnd: "compact x \<Longrightarrow> compact (ssnd\<cdot>x)"
by (rule compactI, simp add: ssnd_below_iff)

lemma compact_spair: "\<lbrakk>compact x; compact y\<rbrakk> \<Longrightarrow> compact (:x, y:)"
by (rule compact_Sprod, simp add: Rep_Sprod_spair strictify_conv_if)

lemma compact_spair_iff:
  "compact (:x, y:) = (x = \<bottom> \<or> y = \<bottom> \<or> (compact x \<and> compact y))"
apply (safe elim!: compact_spair)
apply (drule compact_sfst, simp)
apply (drule compact_ssnd, simp)
apply simp
apply simp
done

subsection {* Properties of @{term ssplit} *}

lemma ssplit1 [simp]: "ssplit\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (simp add: ssplit_def)

lemma ssplit2 [simp]: "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> ssplit\<cdot>f\<cdot>(:x, y:) = f\<cdot>x\<cdot>y"
by (simp add: ssplit_def)

lemma ssplit3 [simp]: "ssplit\<cdot>spair\<cdot>z = z"
by (cases z, simp_all)

subsection {* Strict product preserves flatness *}

instance "**" :: (flat, flat) flat
proof
  fix x y :: "'a \<otimes> 'b"
  assume "x \<sqsubseteq> y" thus "x = \<bottom> \<or> x = y"
    apply (induct x, simp)
    apply (induct y, simp)
    apply (simp add: spair_below_iff flat_below_iff)
    done
qed

subsection {* Strict product is a bifinite domain *}

instantiation "**" :: (bifinite, bifinite) bifinite
begin

definition
  approx_sprod_def:
    "approx = (\<lambda>n. \<Lambda>(:x, y:). (:approx n\<cdot>x, approx n\<cdot>y:))"

instance proof
  fix i :: nat and x :: "'a \<otimes> 'b"
  show "chain (approx :: nat \<Rightarrow> 'a \<otimes> 'b \<rightarrow> 'a \<otimes> 'b)"
    unfolding approx_sprod_def by simp
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx_sprod_def
    by (simp add: lub_distribs eta_cfun)
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    unfolding approx_sprod_def
    by (simp add: ssplit_def strictify_conv_if)
  have "Rep_Sprod ` {x::'a \<otimes> 'b. approx i\<cdot>x = x} \<subseteq> {x. approx i\<cdot>x = x}"
    unfolding approx_sprod_def
    apply (clarify, case_tac x)
     apply (simp add: Rep_Sprod_strict)
    apply (simp add: Rep_Sprod_spair spair_eq_iff)
    done
  hence "finite (Rep_Sprod ` {x::'a \<otimes> 'b. approx i\<cdot>x = x})"
    using finite_fixes_approx by (rule finite_subset)
  thus "finite {x::'a \<otimes> 'b. approx i\<cdot>x = x}"
    by (rule finite_imageD, simp add: inj_on_def Rep_Sprod_inject)
qed

end

lemma approx_spair [simp]:
  "approx i\<cdot>(:x, y:) = (:approx i\<cdot>x, approx i\<cdot>y:)"
unfolding approx_sprod_def
by (simp add: ssplit_def strictify_conv_if)

end
