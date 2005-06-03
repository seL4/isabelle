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

instance unit :: sq_ord ..

defs (overloaded)
  less_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<equiv> True"

instance unit :: po
by intro_classes simp_all

instance unit :: cpo
by intro_classes (simp add: is_lub_def is_ub_def)

instance unit :: pcpo
by intro_classes simp


subsection {* Type @{typ "'a * 'b"} is a partial order *}

instance "*" :: (sq_ord, sq_ord) sq_ord ..

defs (overloaded)
  less_cprod_def: "(op \<sqsubseteq>) \<equiv> \<lambda>p1 p2. (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

lemma refl_less_cprod: "(p::'a * 'b) \<sqsubseteq> p"
by (simp add: less_cprod_def)

lemma antisym_less_cprod: "\<lbrakk>(p1::'a * 'b) \<sqsubseteq> p2; p2 \<sqsubseteq> p1\<rbrakk> \<Longrightarrow> p1 = p2"
apply (unfold less_cprod_def)
apply (rule injective_fst_snd)
apply (fast intro: antisym_less)
apply (fast intro: antisym_less)
done

lemma trans_less_cprod: "\<lbrakk>(p1::'a*'b) \<sqsubseteq> p2; p2 \<sqsubseteq> p3\<rbrakk> \<Longrightarrow> p1 \<sqsubseteq> p3"
apply (unfold less_cprod_def)
apply (fast intro: trans_less)
done

instance "*" :: (cpo, cpo) po
by intro_classes
  (assumption | rule refl_less_cprod antisym_less_cprod trans_less_cprod)+


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

subsection {* Type @{typ "'a * 'b"} is a cpo *}

lemma lub_cprod: 
  "chain S \<Longrightarrow> range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac t = "S i" in surjective_pairing [THEN ssubst])
apply (rule monofun_pair)
apply (rule is_ub_thelub)
apply (erule monofun_fst [THEN ch2ch_monofun])
apply (rule is_ub_thelub)
apply (erule monofun_snd [THEN ch2ch_monofun])
apply (rule_tac t = "u" in surjective_pairing [THEN ssubst])
apply (rule monofun_pair)
apply (rule is_lub_thelub)
apply (erule monofun_fst [THEN ch2ch_monofun])
apply (erule monofun_fst [THEN ub2ub_monofun])
apply (rule is_lub_thelub)
apply (erule monofun_snd [THEN ch2ch_monofun])
apply (erule monofun_snd [THEN ub2ub_monofun])
done

lemma thelub_cprod:
  "chain S \<Longrightarrow> lub (range S) = (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
by (rule lub_cprod [THEN thelubI])

lemma cpo_cprod:
  "chain (S::nat \<Rightarrow> 'a::cpo * 'b::cpo) \<Longrightarrow> \<exists>x. range S <<| x"
by (rule exI, erule lub_cprod)

instance "*" :: (cpo, cpo) cpo
by intro_classes (rule cpo_cprod)

subsection {* Type @{typ "'a * 'b"} is pointed *}

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

lemma contlub_pair1: "contlub (\<lambda>x. (x,y))"
apply (rule contlubI)
apply (subst thelub_cprod)
apply (erule monofun_pair1 [THEN ch2ch_monofun])
apply (simp add: thelub_const)
done

lemma contlub_pair2: "contlub (\<lambda>y. (x, y))"
apply (rule contlubI)
apply (subst thelub_cprod)
apply (erule monofun_pair2 [THEN ch2ch_monofun])
apply (simp add: thelub_const)
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

consts
  cpair  :: "'a \<rightarrow> 'b \<rightarrow> ('a * 'b)" (* continuous pairing *)
  cfst   :: "('a * 'b) \<rightarrow> 'a"
  csnd   :: "('a * 'b) \<rightarrow> 'b"
  csplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a * 'b) \<rightarrow> 'c"

syntax
  "@ctuple" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(1<_,/ _>)")

translations
  "<x, y, z>" == "<x, <y, z>>"
  "<x, y>"    == "cpair$x$y"

defs
  cpair_def:  "cpair  \<equiv> (\<Lambda> x y. (x, y))"
  cfst_def:   "cfst   \<equiv> (\<Lambda> p. fst p)"
  csnd_def:   "csnd   \<equiv> (\<Lambda> p. snd p)"      
  csplit_def: "csplit \<equiv> (\<Lambda> f p. f\<cdot>(cfst\<cdot>p)\<cdot>(csnd\<cdot>p))"

subsection {* Syntax *}

text {* syntax for @{text "LAM <x,y,z>.e"} *}

syntax
  "_LAM" :: "[patterns, 'a \<Rightarrow> 'b] \<Rightarrow> ('a \<rightarrow> 'b)"  ("(3LAM <_>./ _)" [0, 10] 10)

translations
  "LAM <x,y,zs>. b"       == "csplit$(LAM x. LAM <y,zs>. b)"
  "LAM <x,y>. LAM zs. b"  <= "csplit$(LAM x y zs. b)"
  "LAM <x,y>.b"           == "csplit$(LAM x y. b)"

syntax (xsymbols)
  "_LAM" :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3\<Lambda>()<_>./ _)" [0, 10] 10)

text {* syntax for Let *}

constdefs
  CLet :: "'a \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'b"
  "CLet \<equiv> \<Lambda> s f. f\<cdot>s"

nonterminals
  Cletbinds  Cletbind

syntax
  "_Cbind"  :: "[pttrn, 'a] => Cletbind"             ("(2_ =/ _)" 10)
  "_Cbindp" :: "[patterns, 'a] => Cletbind"          ("(2<_> =/ _)" 10)
  ""        :: "Cletbind => Cletbinds"               ("_")
  "_Cbinds" :: "[Cletbind, Cletbinds] => Cletbinds"  ("_;/ _")
  "_CLet"   :: "[Cletbinds, 'a] => 'a"               ("(Let (_)/ in (_))" 10)

translations
  "_CLet (_Cbinds b bs) e"  == "_CLet b (_CLet bs e)"
  "Let x = a in LAM ys. e"  == "CLet$a$(LAM x ys. e)"
  "Let x = a in e"          == "CLet$a$(LAM x. e)"
  "Let <xs> = a in e"       == "CLet$a$(LAM <xs>. e)"

subsection {* Convert all lemmas to the continuous versions *}

lemma cpair_eq_pair: "<x, y> = (x, y)"
by (simp add: cpair_def cont_pair1 cont_pair2)

lemma inject_cpair: "<a,b> = <aa,ba> \<Longrightarrow> a = aa \<and> b = ba"
by (simp add: cpair_eq_pair)

lemma cpair_eq [iff]: "(<a, b> = <a', b'>) = (a = a' \<and> b = b')"
by (simp add: cpair_eq_pair)

lemma cpair_less: "(<a, b> \<sqsubseteq> <a', b'>) = (a \<sqsubseteq> a' \<and> b \<sqsubseteq> b')"
by (simp add: cpair_eq_pair less_cprod_def)

lemma cpair_strict: "<\<bottom>, \<bottom>> = \<bottom>"
by (simp add: cpair_eq_pair inst_cprod_pcpo)

lemma inst_cprod_pcpo2: "\<bottom> = <\<bottom>, \<bottom>>"
by (simp add: cpair_eq_pair inst_cprod_pcpo)

lemma defined_cpair_rev: 
 "<a,b> = \<bottom> \<Longrightarrow> a = \<bottom> \<and> b = \<bottom>"
by (simp add: inst_cprod_pcpo cpair_eq_pair)

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

lemma lub_cprod2: 
  "chain S \<Longrightarrow> range S <<| <\<Squnion>i. cfst\<cdot>(S i), \<Squnion>i. csnd\<cdot>(S i)>"
apply (simp add: cpair_eq_pair cfst_def csnd_def cont_fst cont_snd)
apply (erule lub_cprod)
done

lemma thelub_cprod2:
  "chain S \<Longrightarrow> lub (range S) = <\<Squnion>i. cfst\<cdot>(S i), \<Squnion>i. csnd\<cdot>(S i)>"
by (rule lub_cprod2 [THEN thelubI])

lemma csplit2 [simp]: "csplit\<cdot>f\<cdot><x,y> = f\<cdot>x\<cdot>y"
by (simp add: csplit_def)

lemma csplit3: "csplit\<cdot>cpair\<cdot>z = z"
by (simp add: csplit_def surjective_pairing_Cprod2)

lemmas Cprod_rews = cfst_cpair csnd_cpair csplit2

end
