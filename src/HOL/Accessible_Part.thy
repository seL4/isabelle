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

inductive2
  acc :: "('a => 'a => bool) => 'a => bool"
  for r :: "'a => 'a => bool"
  where
    accI: "(!!y. r y x ==> acc r y) ==> acc r x"

abbreviation
  termi :: "('a => 'a => bool) => 'a => bool" where
  "termi r == acc (r\<inverse>\<inverse>)"


subsection {* Induction rules *}

theorem acc_induct:
  assumes major: "acc r a"
  assumes hyp: "!!x. acc r x ==> \<forall>y. r y x --> P y ==> P x"
  shows "P a"
  apply (rule major [THEN acc.induct])
  apply (rule hyp)
   apply (rule accI)
   apply fast
  apply fast
  done

theorems acc_induct_rule = acc_induct [rule_format, induct set: acc]

theorem acc_downward: "acc r b ==> r a b ==> acc r a"
  apply (erule acc.cases)
  apply fast
  done

lemma not_acc_down:
  assumes na: "\<not> acc R x"
  obtains z where "R z x" and "\<not> acc R z"
proof -
  assume a: "\<And>z. \<lbrakk>R z x; \<not> acc R z\<rbrakk> \<Longrightarrow> thesis"

  show thesis
  proof (cases "\<forall>z. R z x \<longrightarrow> acc R z")
    case True
    hence "\<And>z. R z x \<Longrightarrow> acc R z" by auto
    hence "acc R x"
      by (rule accI)
    with na show thesis ..
  next
    case False then obtain z where "R z x" and "\<not> acc R z"
      by auto
    with a show thesis .
  qed
qed

lemma acc_downwards_aux: "r\<^sup>*\<^sup>* b a ==> acc r a --> acc r b"
  apply (erule rtrancl_induct')
   apply blast
  apply (blast dest: acc_downward)
  done

theorem acc_downwards: "acc r a ==> r\<^sup>*\<^sup>* b a ==> acc r b"
  apply (blast dest: acc_downwards_aux)
  done

theorem acc_wfI: "\<forall>x. acc r x ==> wfP r"
  apply (rule wfPUNIVI)
  apply (induct_tac P x rule: acc_induct)
   apply blast
  apply blast
  done

theorem acc_wfD: "wfP r ==> acc r x"
  apply (erule wfP_induct_rule)
  apply (rule accI)
  apply blast
  done

theorem wf_acc_iff: "wfP r = (\<forall>x. acc r x)"
  apply (blast intro: acc_wfI dest: acc_wfD)
  done


text {* Smaller relations have bigger accessible parts: *}

lemma acc_subset:
  assumes sub: "R1 \<le> R2"
  shows "acc R2 \<le> acc R1"
proof
  fix x assume "acc R2 x"
  then show "acc R1 x"
  proof (induct x)
    fix x
    assume ih: "\<And>y. R2 y x \<Longrightarrow> acc R1 y"
    with sub show "acc R1 x"
      by (blast intro: accI)
  qed
qed


text {* This is a generalized induction theorem that works on
  subsets of the accessible part. *}

lemma acc_subset_induct:
  assumes subset: "D \<le> acc R"
    and dcl: "\<And>x z. \<lbrakk>D x; R z x\<rbrakk> \<Longrightarrow> D z"
    and "D x"
    and istep: "\<And>x. \<lbrakk>D x; (\<And>z. R z x \<Longrightarrow> P z)\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof -
  from subset and `D x`
  have "acc R x" ..
  then show "P x" using `D x`
  proof (induct x)
    fix x
    assume "D x"
      and "\<And>y. R y x \<Longrightarrow> D y \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed

end
