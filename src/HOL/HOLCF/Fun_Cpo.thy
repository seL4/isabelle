(*  Title:      HOL/HOLCF/Fun_Cpo.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section {* Class instances for the full function space *}

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

text {* Properties of chains of functions. *}

lemma fun_chain_iff: "chain S \<longleftrightarrow> (\<forall>x. chain (\<lambda>i. S i x))"
unfolding chain_def fun_below_iff by auto

lemma ch2ch_fun: "chain S \<Longrightarrow> chain (\<lambda>i. S i x)"
by (simp add: chain_def below_fun_def)

lemma ch2ch_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> chain S"
by (simp add: chain_def below_fun_def)

text {* Type @{typ "'a::type => 'b::cpo"} is chain complete *}

lemma is_lub_lambda:
  "(\<And>x. range (\<lambda>i. Y i x) <<| f x) \<Longrightarrow> range Y <<| f"
unfolding is_lub_def is_ub_def below_fun_def by simp

lemma is_lub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> range S <<| (\<lambda>x. \<Squnion>i. S i x)"
apply (rule is_lub_lambda)
apply (rule cpo_lubI)
apply (erule ch2ch_fun)
done

lemma lub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> (\<Squnion>i. S i) = (\<lambda>x. \<Squnion>i. S i x)"
by (rule is_lub_fun [THEN lub_eqI])

instance "fun"  :: (type, cpo) cpo
by intro_classes (rule exI, erule is_lub_fun)

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
by (rule minimal_fun [THEN bottomI, symmetric])

lemma app_strict [simp]: "\<bottom> x = \<bottom>"
by (simp add: inst_fun_pcpo)

lemma lambda_strict: "(\<lambda>x. \<bottom>) = \<bottom>"
by (rule bottomI, rule minimal_fun)

subsection {* Propagation of monotonicity and continuity *}

text {* The lub of a chain of monotone functions is monotone. *}

lemma adm_monofun: "adm monofun"
by (rule admI, simp add: lub_fun fun_chain_iff monofun_def lub_mono)

text {* The lub of a chain of continuous functions is continuous. *}

lemma adm_cont: "adm cont"
by (rule admI, simp add: lub_fun fun_chain_iff)

text {* Function application preserves monotonicity and continuity. *}

lemma mono2mono_fun: "monofun f \<Longrightarrow> monofun (\<lambda>x. f x y)"
by (simp add: monofun_def fun_below_iff)

lemma cont2cont_fun: "cont f \<Longrightarrow> cont (\<lambda>x. f x y)"
apply (rule contI2)
apply (erule cont2mono [THEN mono2mono_fun])
apply (simp add: cont2contlubE lub_fun ch2ch_cont)
done

lemma cont_fun: "cont (\<lambda>f. f x)"
using cont_id by (rule cont2cont_fun)

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
by (simp add: lub_fun ch2ch_lambda)

end
