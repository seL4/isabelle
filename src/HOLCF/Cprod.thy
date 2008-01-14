(*  Title:      HOLCF/Cprod.thy
    ID:         $Id$
    Author:     Franz Regensburger

Partial ordering for cartesian product of HOL products.
*)

header {* The cpo of cartesian products *}

theory Cprod
imports Cfun
begin

defaultsort cpo

subsection {* Type @{typ unit} is a pcpo *}

instantiation unit :: sq_ord
begin

definition
  less_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<equiv> True"

instance ..
end

instance unit :: po
by intro_classes simp_all

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

instantiation "*" :: (sq_ord, sq_ord) sq_ord
begin

definition
  less_cprod_def: "(op \<sqsubseteq>) \<equiv> \<lambda>p1 p2. (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance ..
end

instance "*" :: (po, po) po
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

lemma lub_cprod:
  fixes S :: "nat \<Rightarrow> ('a::cpo \<times> 'b::cpo)"
  assumes S: "chain S"
  shows "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac t = "S i" in surjective_pairing [THEN ssubst])
apply (rule monofun_pair)
apply (rule is_ub_thelub)
apply (rule ch2ch_monofun [OF monofun_fst S])
apply (rule is_ub_thelub)
apply (rule ch2ch_monofun [OF monofun_snd S])
apply (rule_tac t = "u" in surjective_pairing [THEN ssubst])
apply (rule monofun_pair)
apply (rule is_lub_thelub)
apply (rule ch2ch_monofun [OF monofun_fst S])
apply (erule monofun_fst [THEN ub2ub_monofun])
apply (rule is_lub_thelub)
apply (rule ch2ch_monofun [OF monofun_snd S])
apply (erule monofun_snd [THEN ub2ub_monofun])
done

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

lemma least_cprod: "EX x::'a::pcpo * 'b::pcpo. ALL y. x \<sqsubseteq> y"
apply (rule_tac x = "(\<bottom>, \<bottom>)" in exI)
apply (rule minimal_cprod [THEN allI])
done

instance "*" :: (pcpo, pcpo) pcpo
by intro_classes (rule least_cprod)

text {* for compatibility with old HOLCF-Version *}
lemma inst_cprod_pcpo: "UU = (UU,UU)"
by (rule minimal_cprod [THEN UU_I, symmetric])


subsection {* Continuity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

lemma contlub_pair1: "contlub (\<lambda>x. (x, y))"
apply (rule contlubI)
apply (subst thelub_cprod)
apply (erule monofun_pair1 [THEN ch2ch_monofun])
apply simp
done

lemma contlub_pair2: "contlub (\<lambda>y. (x, y))"
apply (rule contlubI)
apply (subst thelub_cprod)
apply (erule monofun_pair2 [THEN ch2ch_monofun])
apply simp
done

lemma cont_pair1: "cont (\<lambda>x. (x, y))"
apply (rule monocontlub2cont)
apply (rule monofun_pair1)
apply (rule contlub_pair1)
done

lemma cont_pair2: "cont (\<lambda>y. (x, y))"
apply (rule monocontlub2cont)
apply (rule monofun_pair2)
apply (rule contlub_pair2)
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

lemma inject_cpair: "<a,b> = <aa,ba> \<Longrightarrow> a = aa \<and> b = ba"
by (simp add: cpair_eq_pair)

lemma cpair_eq [iff]: "(<a, b> = <a', b'>) = (a = a' \<and> b = b')"
by (simp add: cpair_eq_pair)

lemma cpair_less [iff]: "(<a, b> \<sqsubseteq> <a', b'>) = (a \<sqsubseteq> a' \<and> b \<sqsubseteq> b')"
by (simp add: cpair_eq_pair less_cprod_def)

lemma cpair_defined_iff [iff]: "(<x, y> = \<bottom>) = (x = \<bottom> \<and> y = \<bottom>)"
by (simp add: inst_cprod_pcpo cpair_eq_pair)

lemma cpair_strict: "<\<bottom>, \<bottom>> = \<bottom>"
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
by (simp add: inst_cprod_pcpo2)

lemma csnd_strict [simp]: "csnd\<cdot>\<bottom> = \<bottom>"
by (simp add: inst_cprod_pcpo2)

lemma surjective_pairing_Cprod2: "<cfst\<cdot>p, csnd\<cdot>p> = p"
apply (unfold cfst_def csnd_def)
apply (simp add: cont_fst cont_snd cpair_eq_pair)
done

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
apply (intro_classes, clarify)
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
by (simp add: csplit_def surjective_pairing_Cprod2)

lemmas Cprod_rews = cfst_cpair csnd_cpair csplit2

end
