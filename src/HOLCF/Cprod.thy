(*  Title:      HOLCF/Cprod.thy
    ID:         $Id$
    Author:     Franz Regensburger

Partial ordering for cartesian product of HOL products.
*)

header {* The cpo of cartesian products *}

theory Cprod
imports Bifinite
begin

defaultsort cpo

subsection {* Type @{typ unit} is a pcpo *}

instantiation unit :: po
begin

definition
  less_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<equiv> True"

instance
by intro_classes simp_all

end

instance unit :: finite_po ..

instance unit :: pcpo
by intro_classes simp

definition
  unit_when :: "'a \<rightarrow> unit \<rightarrow> 'a" where
  "unit_when = (\<Lambda> a _. a)"

translations
  "\<Lambda>(). t" == "CONST unit_when\<cdot>t"

lemma unit_when [simp]: "unit_when\<cdot>a\<cdot>u = a"
by (simp add: unit_when_def)


subsection {* Product type is a partial order *}

instantiation "*" :: (po, po) po
begin

definition
  less_cprod_def: "(op \<sqsubseteq>) \<equiv> \<lambda>p1 p2. (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance
proof
  fix x :: "'a \<times> 'b"
  show "x \<sqsubseteq> x"
    unfolding less_cprod_def by simp
next
  fix x y :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding less_cprod_def Pair_fst_snd_eq
    by (fast intro: antisym_less)
next
  fix x y z :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding less_cprod_def
    by (fast intro: trans_less)
qed

end

subsection {* Monotonicity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

text {* Pair @{text "(_,_)"}  is monotone in both arguments *}

lemma monofun_pair1: "monofun (\<lambda>x. (x, y))"
by (simp add: monofun_def less_cprod_def)

lemma monofun_pair2: "monofun (\<lambda>y. (x, y))"
by (simp add: monofun_def less_cprod_def)

lemma monofun_pair:
  "\<lbrakk>x1 \<sqsubseteq> x2; y1 \<sqsubseteq> y2\<rbrakk> \<Longrightarrow> (x1, y1) \<sqsubseteq> (x2, y2)"
by (simp add: less_cprod_def)

text {* @{term fst} and @{term snd} are monotone *}

lemma monofun_fst: "monofun fst"
by (simp add: monofun_def less_cprod_def)

lemma monofun_snd: "monofun snd"
by (simp add: monofun_def less_cprod_def)

subsection {* Product type is a cpo *}

lemma is_lub_Pair:
  "\<lbrakk>range X <<| x; range Y <<| y\<rbrakk> \<Longrightarrow> range (\<lambda>i. (X i, Y i)) <<| (x, y)"
apply (rule is_lubI [OF ub_rangeI])
apply (simp add: less_cprod_def is_ub_lub)
apply (frule ub2ub_monofun [OF monofun_fst])
apply (drule ub2ub_monofun [OF monofun_snd])
apply (simp add: less_cprod_def is_lub_lub)
done

lemma lub_cprod:
  fixes S :: "nat \<Rightarrow> ('a::cpo \<times> 'b::cpo)"
  assumes S: "chain S"
  shows "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
proof -
  have "chain (\<lambda>i. fst (S i))"
    using monofun_fst S by (rule ch2ch_monofun)
  hence 1: "range (\<lambda>i. fst (S i)) <<| (\<Squnion>i. fst (S i))"
    by (rule thelubE [OF _ refl])
  have "chain (\<lambda>i. snd (S i))"
    using monofun_snd S by (rule ch2ch_monofun)
  hence 2: "range (\<lambda>i. snd (S i)) <<| (\<Squnion>i. snd (S i))"
    by (rule thelubE [OF _ refl])
  show "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
    using is_lub_Pair [OF 1 2] by simp
qed

lemma thelub_cprod:
  "chain (S::nat \<Rightarrow> 'a::cpo \<times> 'b::cpo)
    \<Longrightarrow> lub (range S) = (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
by (rule lub_cprod [THEN thelubI])

instance "*" :: (cpo, cpo) cpo
proof
  fix S :: "nat \<Rightarrow> ('a \<times> 'b)"
  assume "chain S"
  hence "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
    by (rule lub_cprod)
  thus "\<exists>x. range S <<| x" ..
qed

instance "*" :: (finite_po, finite_po) finite_po ..

subsection {* Product type is pointed *}

lemma minimal_cprod: "(\<bottom>, \<bottom>) \<sqsubseteq> p"
by (simp add: less_cprod_def)

instance "*" :: (pcpo, pcpo) pcpo
by intro_classes (fast intro: minimal_cprod)

lemma inst_cprod_pcpo: "\<bottom> = (\<bottom>, \<bottom>)"
by (rule minimal_cprod [THEN UU_I, symmetric])


subsection {* Continuity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

lemma cont_pair1: "cont (\<lambda>x. (x, y))"
apply (rule contI)
apply (rule is_lub_Pair)
apply (erule thelubE [OF _ refl])
apply (rule lub_const)
done

lemma cont_pair2: "cont (\<lambda>y. (x, y))"
apply (rule contI)
apply (rule is_lub_Pair)
apply (rule lub_const)
apply (erule thelubE [OF _ refl])
done

lemma contlub_fst: "contlub fst"
apply (rule contlubI)
apply (simp add: thelub_cprod)
done

lemma contlub_snd: "contlub snd"
apply (rule contlubI)
apply (simp add: thelub_cprod)
done

lemma cont_fst: "cont fst"
apply (rule monocontlub2cont)
apply (rule monofun_fst)
apply (rule contlub_fst)
done

lemma cont_snd: "cont snd"
apply (rule monocontlub2cont)
apply (rule monofun_snd)
apply (rule contlub_snd)
done

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

lemma cpair_less [iff]: "(<a, b> \<sqsubseteq> <a', b'>) = (a \<sqsubseteq> a' \<and> b \<sqsubseteq> b')"
by (simp add: cpair_eq_pair less_cprod_def)

lemma cpair_defined_iff [iff]: "(<x, y> = \<bottom>) = (x = \<bottom> \<and> y = \<bottom>)"
by (simp add: inst_cprod_pcpo cpair_eq_pair)

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
unfolding inst_cprod_pcpo2 by (rule cfst_cpair)

lemma csnd_strict [simp]: "csnd\<cdot>\<bottom> = \<bottom>"
unfolding inst_cprod_pcpo2 by (rule csnd_cpair)

lemma cpair_cfst_csnd: "\<langle>cfst\<cdot>p, csnd\<cdot>p\<rangle> = p"
by (cases p rule: cprodE, simp)

lemmas surjective_pairing_Cprod2 = cpair_cfst_csnd

lemma less_cprod: "x \<sqsubseteq> y = (cfst\<cdot>x \<sqsubseteq> cfst\<cdot>y \<and> csnd\<cdot>x \<sqsubseteq> csnd\<cdot>y)"
by (simp add: less_cprod_def cfst_def csnd_def cont_fst cont_snd)

lemma eq_cprod: "(x = y) = (cfst\<cdot>x = cfst\<cdot>y \<and> csnd\<cdot>x = csnd\<cdot>y)"
by (auto simp add: po_eq_conv less_cprod)

lemma cfst_less_iff: "cfst\<cdot>x \<sqsubseteq> y = x \<sqsubseteq> <y, csnd\<cdot>x>"
by (simp add: less_cprod)

lemma csnd_less_iff: "csnd\<cdot>x \<sqsubseteq> y = x \<sqsubseteq> <cfst\<cdot>x, y>"
by (simp add: less_cprod)

lemma compact_cfst: "compact x \<Longrightarrow> compact (cfst\<cdot>x)"
by (rule compactI, simp add: cfst_less_iff)

lemma compact_csnd: "compact x \<Longrightarrow> compact (csnd\<cdot>x)"
by (rule compactI, simp add: csnd_less_iff)

lemma compact_cpair: "\<lbrakk>compact x; compact y\<rbrakk> \<Longrightarrow> compact <x, y>"
by (rule compactI, simp add: less_cprod)

lemma compact_cpair_iff [simp]: "compact <x, y> = (compact x \<and> compact y)"
apply (safe intro!: compact_cpair)
apply (drule compact_cfst, simp)
apply (drule compact_csnd, simp)
done

instance "*" :: (chfin, chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (rule_tac p="\<Squnion>i. Y i" in cprodE, simp)
done

lemma lub_cprod2: 
  "chain S \<Longrightarrow> range S <<| <\<Squnion>i. cfst\<cdot>(S i), \<Squnion>i. csnd\<cdot>(S i)>"
apply (simp add: cpair_eq_pair cfst_def csnd_def cont_fst cont_snd)
apply (erule lub_cprod)
done

lemma thelub_cprod2:
  "chain S \<Longrightarrow> lub (range S) = <\<Squnion>i. cfst\<cdot>(S i), \<Squnion>i. csnd\<cdot>(S i)>"
by (rule lub_cprod2 [THEN thelubI])

lemma csplit1 [simp]: "csplit\<cdot>f\<cdot>\<bottom> = f\<cdot>\<bottom>\<cdot>\<bottom>"
by (simp add: csplit_def)

lemma csplit2 [simp]: "csplit\<cdot>f\<cdot><x,y> = f\<cdot>x\<cdot>y"
by (simp add: csplit_def)

lemma csplit3 [simp]: "csplit\<cdot>cpair\<cdot>z = z"
by (simp add: csplit_def cpair_cfst_csnd)

lemmas Cprod_rews = cfst_cpair csnd_cpair csplit2

subsection {* Product type is a bifinite domain *}

instance "*" :: (bifinite_cpo, bifinite_cpo) approx ..

defs (overloaded)
  approx_cprod_def:
    "approx \<equiv> \<lambda>n. \<Lambda>\<langle>x, y\<rangle>. \<langle>approx n\<cdot>x, approx n\<cdot>y\<rangle>"

instance "*" :: (bifinite_cpo, bifinite_cpo) bifinite_cpo
proof
  fix i :: nat and x :: "'a \<times> 'b"
  show "chain (\<lambda>i. approx i\<cdot>x)"
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

instance "*" :: (bifinite, bifinite) bifinite ..

lemma approx_cpair [simp]:
  "approx i\<cdot>\<langle>x, y\<rangle> = \<langle>approx i\<cdot>x, approx i\<cdot>y\<rangle>"
unfolding approx_cprod_def by simp

lemma cfst_approx: "cfst\<cdot>(approx i\<cdot>p) = approx i\<cdot>(cfst\<cdot>p)"
by (cases p rule: cprodE, simp)

lemma csnd_approx: "csnd\<cdot>(approx i\<cdot>p) = approx i\<cdot>(csnd\<cdot>p)"
by (cases p rule: cprodE, simp)

end
