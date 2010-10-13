(*  Title:      HOLCF/Fun_Cpo.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

header {* Class instances for the full function space *}

theory Fun_Cpo
imports Adm
begin

subsection {* Full function space is a partial order *}

instantiation "fun"  :: (type, below) below
begin

definition
  below_fun_def: "(op \<sqsubseteq>) \<equiv> (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x)"

instance ..
end

instance "fun" :: (type, po) po
proof
  fix f :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> f"
    by (simp add: below_fun_def)
next
  fix f g :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> f" thus "f = g"
    by (simp add: below_fun_def fun_eq_iff below_antisym)
next
  fix f g h :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> h" thus "f \<sqsubseteq> h"
    unfolding below_fun_def by (fast elim: below_trans)
qed

lemma fun_below_iff: "f \<sqsubseteq> g \<longleftrightarrow> (\<forall>x. f x \<sqsubseteq> g x)"
by (simp add: below_fun_def)

lemma fun_belowI: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> f \<sqsubseteq> g"
by (simp add: below_fun_def)

lemma fun_belowD: "f \<sqsubseteq> g \<Longrightarrow> f x \<sqsubseteq> g x"
by (simp add: below_fun_def)

subsection {* Full function space is chain complete *}

text {* Function application is monotone. *}

lemma monofun_app: "monofun (\<lambda>f. f x)"
by (rule monofunI, simp add: below_fun_def)

text {* Properties of chains of functions. *}

lemma fun_chain_iff: "chain S \<longleftrightarrow> (\<forall>x. chain (\<lambda>i. S i x))"
unfolding chain_def fun_below_iff by auto

lemma ch2ch_fun: "chain S \<Longrightarrow> chain (\<lambda>i. S i x)"
by (simp add: chain_def below_fun_def)

lemma ch2ch_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> chain S"
by (simp add: chain_def below_fun_def)

text {* upper bounds of function chains yield upper bound in the po range *}

lemma ub2ub_fun:
  "range S <| u \<Longrightarrow> range (\<lambda>i. S i x) <| u x"
by (auto simp add: is_ub_def below_fun_def)

text {* Type @{typ "'a::type => 'b::cpo"} is chain complete *}

lemma is_lub_lambda:
  "(\<And>x. range (\<lambda>i. Y i x) <<| f x) \<Longrightarrow> range Y <<| f"
unfolding is_lub_def is_ub_def below_fun_def by simp

lemma lub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> range S <<| (\<lambda>x. \<Squnion>i. S i x)"
apply (rule is_lub_lambda)
apply (rule cpo_lubI)
apply (erule ch2ch_fun)
done

lemma thelub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> (\<Squnion>i. S i) = (\<lambda>x. \<Squnion>i. S i x)"
by (rule lub_fun [THEN thelubI])

instance "fun"  :: (type, cpo) cpo
by intro_classes (rule exI, erule lub_fun)

subsection {* Chain-finiteness of function space *}

lemma maxinch2maxinch_lambda:
  "(\<And>x. max_in_chain n (\<lambda>i. S i x)) \<Longrightarrow> max_in_chain n S"
unfolding max_in_chain_def fun_eq_iff by simp

lemma maxinch_mono:
  "\<lbrakk>max_in_chain i Y; i \<le> j\<rbrakk> \<Longrightarrow> max_in_chain j Y"
unfolding max_in_chain_def
proof (intro allI impI)
  fix k
  assume Y: "\<forall>n\<ge>i. Y i = Y n"
  assume ij: "i \<le> j"
  assume jk: "j \<le> k"
  from ij jk have ik: "i \<le> k" by simp
  from Y ij have Yij: "Y i = Y j" by simp
  from Y ik have Yik: "Y i = Y k" by simp
  from Yij Yik show "Y j = Y k" by auto
qed

instance "fun" :: (finite, chfin) chfin
proof
  fix Y :: "nat \<Rightarrow> 'a \<Rightarrow> 'b"
  let ?n = "\<lambda>x. LEAST n. max_in_chain n (\<lambda>i. Y i x)"
  assume "chain Y"
  hence "\<And>x. chain (\<lambda>i. Y i x)"
    by (rule ch2ch_fun)
  hence "\<And>x. \<exists>n. max_in_chain n (\<lambda>i. Y i x)"
    by (rule chfin)
  hence "\<And>x. max_in_chain (?n x) (\<lambda>i. Y i x)"
    by (rule LeastI_ex)
  hence "\<And>x. max_in_chain (Max (range ?n)) (\<lambda>i. Y i x)"
    by (rule maxinch_mono [OF _ Max_ge], simp_all)
  hence "max_in_chain (Max (range ?n)) Y"
    by (rule maxinch2maxinch_lambda)
  thus "\<exists>n. max_in_chain n Y" ..
qed

instance "fun" :: (finite, finite_po) finite_po ..

instance "fun" :: (type, discrete_cpo) discrete_cpo
proof
  fix f g :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> g \<longleftrightarrow> f = g" 
    unfolding fun_below_iff fun_eq_iff
    by simp
qed

subsection {* Full function space is pointed *}

lemma minimal_fun: "(\<lambda>x. \<bottom>) \<sqsubseteq> f"
by (simp add: below_fun_def)

instance "fun"  :: (type, pcpo) pcpo
by default (fast intro: minimal_fun)

lemma inst_fun_pcpo: "\<bottom> = (\<lambda>x. \<bottom>)"
by (rule minimal_fun [THEN UU_I, symmetric])

lemma app_strict [simp]: "\<bottom> x = \<bottom>"
by (simp add: inst_fun_pcpo)

lemma lambda_strict: "(\<lambda>x. \<bottom>) = \<bottom>"
by (rule UU_I, rule minimal_fun)

subsection {* Propagation of monotonicity and continuity *}

text {* The lub of a chain of monotone functions is monotone. *}

lemma adm_monofun: "adm monofun"
by (rule admI, simp add: thelub_fun fun_chain_iff monofun_def lub_mono)

text {* The lub of a chain of continuous functions is continuous. *}

lemma adm_cont: "adm cont"
by (rule admI, simp add: thelub_fun fun_chain_iff)

text {* Function application preserves monotonicity and continuity. *}

lemma mono2mono_fun: "monofun f \<Longrightarrow> monofun (\<lambda>x. f x y)"
by (simp add: monofun_def fun_below_iff)

lemma cont2cont_fun: "cont f \<Longrightarrow> cont (\<lambda>x. f x y)"
apply (rule contI2)
apply (erule cont2mono [THEN mono2mono_fun])
apply (simp add: cont2contlubE thelub_fun ch2ch_cont)
done

text {*
  Lambda abstraction preserves monotonicity and continuity.
  (Note @{text "(\<lambda>x. \<lambda>y. f x y) = f"}.)
*}

lemma mono2mono_lambda:
  assumes f: "\<And>y. monofun (\<lambda>x. f x y)" shows "monofun f"
using f by (simp add: monofun_def fun_below_iff)

lemma cont2cont_lambda [simp]:
  assumes f: "\<And>y. cont (\<lambda>x. f x y)" shows "cont f"
by (rule contI, rule is_lub_lambda, rule contE [OF f])

text {* What D.A.Schmidt calls continuity of abstraction; never used here *}

lemma contlub_lambda:
  "(\<And>x::'a::type. chain (\<lambda>i. S i x::'b::cpo))
    \<Longrightarrow> (\<lambda>x. \<Squnion>i. S i x) = (\<Squnion>i. (\<lambda>x. S i x))"
by (simp add: thelub_fun ch2ch_lambda)

end
