(*  Title:      HOLCF/Cprod.thy
    Author:     Franz Regensburger
*)

header {* The cpo of cartesian products *}

theory Cprod
imports Bifinite
begin

defaultsort cpo

subsection {* Type @{typ unit} is a pcpo *}

definition
  unit_when :: "'a \<rightarrow> unit \<rightarrow> 'a" where
  "unit_when = (\<Lambda> a _. a)"

translations
  "\<Lambda>(). t" == "CONST unit_when\<cdot>t"

lemma unit_when [simp]: "unit_when\<cdot>a\<cdot>u = a"
by (simp add: unit_when_def)

subsection {* Continuous versions of constants *}

definition
  cpair :: "'a \<rightarrow> 'b \<rightarrow> ('a * 'b)"  -- {* continuous pairing *}  where
  "cpair = (\<Lambda> x y. (x, y))"

definition
  cfst :: "('a * 'b) \<rightarrow> 'a" where
  "cfst = (\<Lambda> p. fst p)"

definition
  csnd :: "('a * 'b) \<rightarrow> 'b" where
  "csnd = (\<Lambda> p. snd p)"      

definition
  csplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a * 'b) \<rightarrow> 'c" where
  "csplit = (\<Lambda> f p. f\<cdot>(cfst\<cdot>p)\<cdot>(csnd\<cdot>p))"

syntax
  "_ctuple" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(1<_,/ _>)")

syntax (xsymbols)
  "_ctuple" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(1\<langle>_,/ _\<rangle>)")

translations
  "\<langle>x, y, z\<rangle>" == "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"    == "CONST cpair\<cdot>x\<cdot>y"

translations
  "\<Lambda>(CONST cpair\<cdot>x\<cdot>y). t" == "CONST csplit\<cdot>(\<Lambda> x y. t)"


subsection {* Convert all lemmas to the continuous versions *}

lemma cpair_eq_pair: "<x, y> = (x, y)"
by (simp add: cpair_def cont_pair1 cont_pair2)

lemma pair_eq_cpair: "(x, y) = <x, y>"
by (simp add: cpair_def cont_pair1 cont_pair2)

lemma inject_cpair: "<a,b> = <aa,ba> \<Longrightarrow> a = aa \<and> b = ba"
by (simp add: cpair_eq_pair)

lemma cpair_eq [iff]: "(<a, b> = <a', b'>) = (a = a' \<and> b = b')"
by (simp add: cpair_eq_pair)

lemma cpair_below [iff]: "(<a, b> \<sqsubseteq> <a', b'>) = (a \<sqsubseteq> a' \<and> b \<sqsubseteq> b')"
by (simp add: cpair_eq_pair)

lemma cpair_defined_iff [iff]: "(<x, y> = \<bottom>) = (x = \<bottom> \<and> y = \<bottom>)"
by (simp add: cpair_eq_pair)

lemma cpair_strict [simp]: "\<langle>\<bottom>, \<bottom>\<rangle> = \<bottom>"
by simp

lemma inst_cprod_pcpo2: "\<bottom> = <\<bottom>, \<bottom>>"
by (rule cpair_strict [symmetric])

lemma defined_cpair_rev: 
 "<a,b> = \<bottom> \<Longrightarrow> a = \<bottom> \<and> b = \<bottom>"
by simp

lemma Exh_Cprod2: "\<exists>a b. z = <a, b>"
by (simp add: cpair_eq_pair)

lemma cprodE: "\<lbrakk>\<And>x y. p = <x, y> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (cut_tac Exh_Cprod2, auto)

lemma cfst_cpair [simp]: "cfst\<cdot><x, y> = x"
by (simp add: cpair_eq_pair cfst_def cont_fst)

lemma csnd_cpair [simp]: "csnd\<cdot><x, y> = y"
by (simp add: cpair_eq_pair csnd_def cont_snd)

lemma cfst_strict [simp]: "cfst\<cdot>\<bottom> = \<bottom>"
by (simp add: cfst_def)

lemma csnd_strict [simp]: "csnd\<cdot>\<bottom> = \<bottom>"
by (simp add: csnd_def)

lemma cpair_cfst_csnd: "\<langle>cfst\<cdot>p, csnd\<cdot>p\<rangle> = p"
by (cases p rule: cprodE, simp)

lemmas surjective_pairing_Cprod2 = cpair_cfst_csnd

lemma below_cprod: "x \<sqsubseteq> y = (cfst\<cdot>x \<sqsubseteq> cfst\<cdot>y \<and> csnd\<cdot>x \<sqsubseteq> csnd\<cdot>y)"
by (simp add: below_prod_def cfst_def csnd_def cont_fst cont_snd)

lemma eq_cprod: "(x = y) = (cfst\<cdot>x = cfst\<cdot>y \<and> csnd\<cdot>x = csnd\<cdot>y)"
by (auto simp add: po_eq_conv below_cprod)

lemma cfst_below_iff: "cfst\<cdot>x \<sqsubseteq> y = x \<sqsubseteq> <y, csnd\<cdot>x>"
by (simp add: below_cprod)

lemma csnd_below_iff: "csnd\<cdot>x \<sqsubseteq> y = x \<sqsubseteq> <cfst\<cdot>x, y>"
by (simp add: below_cprod)

lemma compact_cfst: "compact x \<Longrightarrow> compact (cfst\<cdot>x)"
by (rule compactI, simp add: cfst_below_iff)

lemma compact_csnd: "compact x \<Longrightarrow> compact (csnd\<cdot>x)"
by (rule compactI, simp add: csnd_below_iff)

lemma compact_cpair: "\<lbrakk>compact x; compact y\<rbrakk> \<Longrightarrow> compact <x, y>"
by (simp add: cpair_eq_pair)

lemma compact_cpair_iff [simp]: "compact <x, y> = (compact x \<and> compact y)"
by (simp add: cpair_eq_pair)

lemma lub_cprod2: 
  "chain S \<Longrightarrow> range S <<| <\<Squnion>i. cfst\<cdot>(S i), \<Squnion>i. csnd\<cdot>(S i)>"
apply (simp add: cpair_eq_pair cfst_def csnd_def cont_fst cont_snd)
apply (erule lub_cprod)
done

lemma thelub_cprod2:
  "chain S \<Longrightarrow> (\<Squnion>i. S i) = <\<Squnion>i. cfst\<cdot>(S i), \<Squnion>i. csnd\<cdot>(S i)>"
by (rule lub_cprod2 [THEN thelubI])

lemma csplit1 [simp]: "csplit\<cdot>f\<cdot>\<bottom> = f\<cdot>\<bottom>\<cdot>\<bottom>"
by (simp add: csplit_def)

lemma csplit2 [simp]: "csplit\<cdot>f\<cdot><x,y> = f\<cdot>x\<cdot>y"
by (simp add: csplit_def)

lemma csplit3 [simp]: "csplit\<cdot>cpair\<cdot>z = z"
by (simp add: csplit_def cpair_cfst_csnd)

lemmas Cprod_rews = cfst_cpair csnd_cpair csplit2

subsection {* Product type is a bifinite domain *}

instantiation "*" :: (profinite, profinite) profinite
begin

definition
  approx_cprod_def:
    "approx = (\<lambda>n. \<Lambda>\<langle>x, y\<rangle>. \<langle>approx n\<cdot>x, approx n\<cdot>y\<rangle>)"

instance proof
  fix i :: nat and x :: "'a \<times> 'b"
  show "chain (approx :: nat \<Rightarrow> 'a \<times> 'b \<rightarrow> 'a \<times> 'b)"
    unfolding approx_cprod_def by simp
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx_cprod_def
    by (simp add: lub_distribs eta_cfun)
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    unfolding approx_cprod_def csplit_def by simp
  have "{x::'a \<times> 'b. approx i\<cdot>x = x} \<subseteq>
        {x::'a. approx i\<cdot>x = x} \<times> {x::'b. approx i\<cdot>x = x}"
    unfolding approx_cprod_def
    by (clarsimp simp add: pair_eq_cpair)
  thus "finite {x::'a \<times> 'b. approx i\<cdot>x = x}"
    by (rule finite_subset,
        intro finite_cartesian_product finite_fixes_approx)
qed

end

instance "*" :: (bifinite, bifinite) bifinite ..

lemma approx_cpair [simp]:
  "approx i\<cdot>\<langle>x, y\<rangle> = \<langle>approx i\<cdot>x, approx i\<cdot>y\<rangle>"
unfolding approx_cprod_def by simp

lemma cfst_approx: "cfst\<cdot>(approx i\<cdot>p) = approx i\<cdot>(cfst\<cdot>p)"
by (cases p rule: cprodE, simp)

lemma csnd_approx: "csnd\<cdot>(approx i\<cdot>p) = approx i\<cdot>(csnd\<cdot>p)"
by (cases p rule: cprodE, simp)

end
