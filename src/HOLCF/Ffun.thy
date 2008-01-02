(*  Title:      HOLCF/FunCpo.thy
    ID:         $Id$
    Author:     Franz Regensburger

Definition of the partial ordering for the type of all functions => (fun)

Class instance of  => (fun) for class pcpo.
*)

header {* Class instances for the full function space *}

theory Ffun
imports Pcpo
begin

subsection {* Full function space is a partial order *}

instantiation "fun"  :: (type, sq_ord) sq_ord
begin

definition
  less_fun_def: "(op \<sqsubseteq>) \<equiv> (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x)"  

instance ..
end

instance "fun" :: (type, po) po
proof
  fix f :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> f"
    by (simp add: less_fun_def)
next
  fix f g :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> f" thus "f = g"
    by (simp add: less_fun_def expand_fun_eq antisym_less)
next
  fix f g h :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> h" thus "f \<sqsubseteq> h"
    unfolding less_fun_def by (fast elim: trans_less)
qed

text {* make the symbol @{text "<<"} accessible for type fun *}

lemma expand_fun_less: "(f \<sqsubseteq> g) = (\<forall>x. f x \<sqsubseteq> g x)"
by (simp add: less_fun_def)

lemma less_fun_ext: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> f \<sqsubseteq> g"
by (simp add: less_fun_def)

subsection {* Full function space is chain complete *}

text {* chains of functions yield chains in the po range *}

lemma ch2ch_fun: "chain S \<Longrightarrow> chain (\<lambda>i. S i x)"
by (simp add: chain_def less_fun_def)

lemma ch2ch_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> chain S"
by (simp add: chain_def less_fun_def)


text {* upper bounds of function chains yield upper bound in the po range *}

lemma ub2ub_fun:
  "range (S::nat \<Rightarrow> 'a \<Rightarrow> 'b::po) <| u \<Longrightarrow> range (\<lambda>i. S i x) <| u x"
by (auto simp add: is_ub_def less_fun_def)

text {* Type @{typ "'a::type => 'b::cpo"} is chain complete *}

lemma lub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> range S <<| (\<lambda>x. \<Squnion>i. S i x)"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule less_fun_ext)
apply (rule is_ub_thelub)
apply (erule ch2ch_fun)
apply (rule less_fun_ext)
apply (rule is_lub_thelub)
apply (erule ch2ch_fun)
apply (erule ub2ub_fun)
done

lemma thelub_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo)
    \<Longrightarrow> lub (range S) = (\<lambda>x. \<Squnion>i. S i x)"
by (rule lub_fun [THEN thelubI])

lemma cpo_fun:
  "chain (S::nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo) \<Longrightarrow> \<exists>x. range S <<| x"
by (rule exI, erule lub_fun)

instance "fun"  :: (type, cpo) cpo
by intro_classes (rule cpo_fun)

subsection {* Full function space is pointed *}

lemma minimal_fun: "(\<lambda>x. \<bottom>) \<sqsubseteq> f"
by (simp add: less_fun_def)

lemma least_fun: "\<exists>x::'a \<Rightarrow> 'b::pcpo. \<forall>y. x \<sqsubseteq> y"
apply (rule_tac x = "\<lambda>x. \<bottom>" in exI)
apply (rule minimal_fun [THEN allI])
done

instance "fun"  :: (type, pcpo) pcpo
by intro_classes (rule least_fun)

text {* for compatibility with old HOLCF-Version *}
lemma inst_fun_pcpo: "\<bottom> = (\<lambda>x. \<bottom>)"
by (rule minimal_fun [THEN UU_I, symmetric])

text {* function application is strict in the left argument *}
lemma app_strict [simp]: "\<bottom> x = \<bottom>"
by (simp add: inst_fun_pcpo)

end

