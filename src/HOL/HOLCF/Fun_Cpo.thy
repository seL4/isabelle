(*  Title:      HOL/HOLCF/Fun_Cpo.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section \<open>Class instances for the full function space\<close>

theory Fun_Cpo
  imports Adm
begin

subsection \<open>Full function space is a partial order\<close>

instantiation "fun"  :: (type, below) below
begin

definition below_fun_def: "(\<sqsubseteq>) \<equiv> (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x)"

instance ..
end

instance "fun" :: (type, po) po
proof
  fix f :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> f"
    by (simp add: below_fun_def)
next
  fix f g :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> f" then show "f = g"
    by (simp add: below_fun_def fun_eq_iff below_antisym)
next
  fix f g h :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> h" then show "f \<sqsubseteq> h"
    unfolding below_fun_def by (fast elim: below_trans)
qed

lemma fun_below_iff: "f \<sqsubseteq> g \<longleftrightarrow> (\<forall>x. f x \<sqsubseteq> g x)"
  by (simp add: below_fun_def)

lemma fun_belowI: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> f \<sqsubseteq> g"
  by (simp add: below_fun_def)

lemma fun_belowD: "f \<sqsubseteq> g \<Longrightarrow> f x \<sqsubseteq> g x"
  by (simp add: below_fun_def)


subsection \<open>Full function space is chain complete\<close>

text \<open>Properties of chains of functions.\<close>

lemma fun_chain_iff: "chain S \<longleftrightarrow> (\<forall>x. chain (\<lambda>i. S i x))"
  by (auto simp: chain_def fun_below_iff)

lemma ch2ch_fun: "chain S \<Longrightarrow> chain (\<lambda>i. S i x)"
  by (simp add: chain_def below_fun_def)

lemma ch2ch_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> chain S"
  by (simp add: chain_def below_fun_def)

text \<open>Type @{typ "'a::type \<Rightarrow> 'b::cpo"} is chain complete\<close>

lemma is_lub_lambda: "(\<And>x. range (\<lambda>i. Y i x) <<| f x) \<Longrightarrow> range Y <<| f"
  by (simp add: is_lub_def is_ub_def below_fun_def)

lemma is_lub_fun: "chain S \<Longrightarrow> range S <<| (\<lambda>x. \<Squnion>i. S i x)"
  for S :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  apply (rule is_lub_lambda)
  apply (rule cpo_lubI)
  apply (erule ch2ch_fun)
  done

lemma lub_fun: "chain S \<Longrightarrow> (\<Squnion>i. S i) = (\<lambda>x. \<Squnion>i. S i x)"
  for S :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  by (rule is_lub_fun [THEN lub_eqI])

instance "fun"  :: (type, cpo) cpo
  by intro_classes (rule exI, erule is_lub_fun)

instance "fun" :: (type, discrete_cpo) discrete_cpo
proof
  fix f g :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> g \<longleftrightarrow> f = g"
    by (simp add: fun_below_iff fun_eq_iff)
qed


subsection \<open>Full function space is pointed\<close>

lemma minimal_fun: "(\<lambda>x. \<bottom>) \<sqsubseteq> f"
  by (simp add: below_fun_def)

instance "fun"  :: (type, pcpo) pcpo
  by standard (fast intro: minimal_fun)

lemma inst_fun_pcpo: "\<bottom> = (\<lambda>x. \<bottom>)"
  by (rule minimal_fun [THEN bottomI, symmetric])

lemma app_strict [simp]: "\<bottom> x = \<bottom>"
  by (simp add: inst_fun_pcpo)

lemma lambda_strict: "(\<lambda>x. \<bottom>) = \<bottom>"
  by (rule bottomI, rule minimal_fun)


subsection \<open>Propagation of monotonicity and continuity\<close>

text \<open>The lub of a chain of monotone functions is monotone.\<close>

lemma adm_monofun: "adm monofun"
  by (rule admI) (simp add: lub_fun fun_chain_iff monofun_def lub_mono)

text \<open>The lub of a chain of continuous functions is continuous.\<close>

lemma adm_cont: "adm cont"
  by (rule admI) (simp add: lub_fun fun_chain_iff)

text \<open>Function application preserves monotonicity and continuity.\<close>

lemma mono2mono_fun: "monofun f \<Longrightarrow> monofun (\<lambda>x. f x y)"
  by (simp add: monofun_def fun_below_iff)

lemma cont2cont_fun: "cont f \<Longrightarrow> cont (\<lambda>x. f x y)"
  apply (rule contI2)
   apply (erule cont2mono [THEN mono2mono_fun])
  apply (simp add: cont2contlubE lub_fun ch2ch_cont)
  done

lemma cont_fun: "cont (\<lambda>f. f x)"
  using cont_id by (rule cont2cont_fun)

text \<open>
  Lambda abstraction preserves monotonicity and continuity.
  (Note \<open>(\<lambda>x. \<lambda>y. f x y) = f\<close>.)
\<close>

lemma mono2mono_lambda: "(\<And>y. monofun (\<lambda>x. f x y)) \<Longrightarrow> monofun f"
  by (simp add: monofun_def fun_below_iff)

lemma cont2cont_lambda [simp]:
  assumes f: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont f"
  by (rule contI, rule is_lub_lambda, rule contE [OF f])

text \<open>What D.A.Schmidt calls continuity of abstraction; never used here\<close>

lemma contlub_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> (\<lambda>x. \<Squnion>i. S i x) = (\<Squnion>i. (\<lambda>x. S i x))"
  for S :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  by (simp add: lub_fun ch2ch_lambda)

end
