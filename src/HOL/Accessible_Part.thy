(*  Title:      HOL/Accessible_Part.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* The accessible part of a relation *}

theory Accessible_Part
imports Wellfounded_Recursion
begin

subsection {* Inductive definition *}

text {*
 Inductive definition of the accessible part @{term "acc r"} of a
 relation; see also \cite{paulin-tlca}.
*}

consts
  acc :: "('a \<times> 'a) set => 'a set"
inductive "acc r"
  intros
    accI: "(!!y. (y, x) \<in> r ==> y \<in> acc r) ==> x \<in> acc r"

abbreviation
  termi :: "('a \<times> 'a) set => 'a set"
  "termi r == acc (r\<inverse>)"


subsection {* Induction rules *}

theorem acc_induct:
  assumes major: "a \<in> acc r"
  assumes hyp: "!!x. x \<in> acc r ==> \<forall>y. (y, x) \<in> r --> P y ==> P x"
  shows "P a"
  apply (rule major [THEN acc.induct])
  apply (rule hyp)
   apply (rule accI)
   apply fast
  apply fast
  done

theorems acc_induct_rule = acc_induct [rule_format, induct set: acc]

theorem acc_downward: "b \<in> acc r ==> (a, b) \<in> r ==> a \<in> acc r"
  apply (erule acc.elims)
  apply fast
  done

lemma acc_downwards_aux: "(b, a) \<in> r\<^sup>* ==> a \<in> acc r --> b \<in> acc r"
  apply (erule rtrancl_induct)
   apply blast
  apply (blast dest: acc_downward)
  done

theorem acc_downwards: "a \<in> acc r ==> (b, a) \<in> r\<^sup>* ==> b \<in> acc r"
  apply (blast dest: acc_downwards_aux)
  done

theorem acc_wfI: "\<forall>x. x \<in> acc r ==> wf r"
  apply (rule wfUNIVI)
  apply (induct_tac P x rule: acc_induct)
   apply blast
  apply blast
  done

theorem acc_wfD: "wf r ==> x \<in> acc r"
  apply (erule wf_induct)
  apply (rule accI)
  apply blast
  done

theorem wf_acc_iff: "wf r = (\<forall>x. x \<in> acc r)"
  apply (blast intro: acc_wfI dest: acc_wfD)
  done


text {* Smaller relations have bigger accessible parts: *}

lemma acc_subset:
  assumes sub: "R1 \<subseteq> R2"
  shows "acc R2 \<subseteq> acc R1"
proof
  fix x assume "x \<in> acc R2"
  then show "x \<in> acc R1"
  proof (induct x)
    fix x
    assume ih: "\<And>y. (y, x) \<in> R2 \<Longrightarrow> y \<in> acc R1"
    with sub show "x \<in> acc R1"
      by (blast intro:accI)
  qed
qed


text {* This is a generalized induction theorem that works on
  subsets of the accessible part. *}

lemma acc_subset_induct:
  assumes subset: "D \<subseteq> acc R"
    and dcl: "\<And>x z. \<lbrakk>x \<in> D; (z, x)\<in>R\<rbrakk> \<Longrightarrow> z \<in> D"
    and "x \<in> D"
    and istep: "\<And>x. \<lbrakk>x \<in> D; (\<And>z. (z, x)\<in>R \<Longrightarrow> P z)\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof -
  from `x \<in> D` and subset 
  have "x \<in> acc R" ..
  then show "P x" using `x \<in> D`
  proof (induct x)
    fix x
    assume "x \<in> D"
      and "\<And>y. (y, x) \<in> R \<Longrightarrow> y \<in> D \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed

end
