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

inductive_set
  acc :: "('a * 'a) set => 'a set"
  for r :: "('a * 'a) set"
  where
    accI: "(!!y. (y, x) : r ==> y : acc r) ==> x : acc r"

abbreviation
  termip :: "('a => 'a => bool) => 'a => bool" where
  "termip r == accp (r\<inverse>\<inverse>)"

abbreviation
  termi :: "('a * 'a) set => 'a set" where
  "termi r == acc (r\<inverse>)"

lemmas accpI = accp.accI

subsection {* Induction rules *}

theorem accp_induct:
  assumes major: "accp r a"
  assumes hyp: "!!x. accp r x ==> \<forall>y. r y x --> P y ==> P x"
  shows "P a"
  apply (rule major [THEN accp.induct])
  apply (rule hyp)
   apply (rule accp.accI)
   apply fast
  apply fast
  done

theorems accp_induct_rule = accp_induct [rule_format, induct set: accp]

theorem accp_downward: "accp r b ==> r a b ==> accp r a"
  apply (erule accp.cases)
  apply fast
  done

lemma not_accp_down:
  assumes na: "\<not> accp R x"
  obtains z where "R z x" and "\<not> accp R z"
proof -
  assume a: "\<And>z. \<lbrakk>R z x; \<not> accp R z\<rbrakk> \<Longrightarrow> thesis"

  show thesis
  proof (cases "\<forall>z. R z x \<longrightarrow> accp R z")
    case True
    hence "\<And>z. R z x \<Longrightarrow> accp R z" by auto
    hence "accp R x"
      by (rule accp.accI)
    with na show thesis ..
  next
    case False then obtain z where "R z x" and "\<not> accp R z"
      by auto
    with a show thesis .
  qed
qed

lemma accp_downwards_aux: "r\<^sup>*\<^sup>* b a ==> accp r a --> accp r b"
  apply (erule rtranclp_induct)
   apply blast
  apply (blast dest: accp_downward)
  done

theorem accp_downwards: "accp r a ==> r\<^sup>*\<^sup>* b a ==> accp r b"
  apply (blast dest: accp_downwards_aux)
  done

theorem accp_wfPI: "\<forall>x. accp r x ==> wfP r"
  apply (rule wfPUNIVI)
  apply (induct_tac P x rule: accp_induct)
   apply blast
  apply blast
  done

theorem accp_wfPD: "wfP r ==> accp r x"
  apply (erule wfP_induct_rule)
  apply (rule accp.accI)
  apply blast
  done

theorem wfP_accp_iff: "wfP r = (\<forall>x. accp r x)"
  apply (blast intro: accp_wfPI dest: accp_wfPD)
  done


text {* Smaller relations have bigger accessible parts: *}

lemma accp_subset:
  assumes sub: "R1 \<le> R2"
  shows "accp R2 \<le> accp R1"
proof
  fix x assume "accp R2 x"
  then show "accp R1 x"
  proof (induct x)
    fix x
    assume ih: "\<And>y. R2 y x \<Longrightarrow> accp R1 y"
    with sub show "accp R1 x"
      by (blast intro: accp.accI)
  qed
qed


text {* This is a generalized induction theorem that works on
  subsets of the accessible part. *}

lemma accp_subset_induct:
  assumes subset: "D \<le> accp R"
    and dcl: "\<And>x z. \<lbrakk>D x; R z x\<rbrakk> \<Longrightarrow> D z"
    and "D x"
    and istep: "\<And>x. \<lbrakk>D x; (\<And>z. R z x \<Longrightarrow> P z)\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof -
  from subset and `D x`
  have "accp R x" ..
  then show "P x" using `D x`
  proof (induct x)
    fix x
    assume "D x"
      and "\<And>y. R y x \<Longrightarrow> D y \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed


text {* Set versions of the above theorems *}

lemmas acc_induct = accp_induct [to_set]

lemmas acc_induct_rule = acc_induct [rule_format, induct set: acc]

lemmas acc_downward = accp_downward [to_set]

lemmas not_acc_down = not_accp_down [to_set]

lemmas acc_downwards_aux = accp_downwards_aux [to_set]

lemmas acc_downwards = accp_downwards [to_set]

lemmas acc_wfI = accp_wfPI [to_set]

lemmas acc_wfD = accp_wfPD [to_set]

lemmas wf_acc_iff = wfP_accp_iff [to_set]

lemmas acc_subset = accp_subset [to_set]

lemmas acc_subset_induct = accp_subset_induct [to_set]

end
