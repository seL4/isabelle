(*  Title:      HOL/Library/Accessible_Part.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {*
 \title{The accessible part of a relation}
 \author{Lawrence C Paulson}
*}

theory Accessible_Part = Main:


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

syntax
  termi :: "('a \<times> 'a) set => 'a set"
translations
  "termi r" == "acc (r\<inverse>)"


subsection {* Induction rules *}

theorem acc_induct:
  "a \<in> acc r ==>
    (!!x. x \<in> acc r ==> \<forall>y. (y, x) \<in> r --> P y ==> P x) ==> P a"
proof -
  assume major: "a \<in> acc r"
  assume hyp: "!!x. x \<in> acc r ==> \<forall>y. (y, x) \<in> r --> P y ==> P x"
  show ?thesis
    apply (rule major [THEN acc.induct])
    apply (rule hyp)
     apply (rule accI)
     apply fast
    apply fast
    done
qed

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

end
