(*  Title:      HOL/ex/Acc.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

header {* The accessible part of a relation *}

theory Acc = Main:

consts
  acc  :: "('a \<times> 'a) set => 'a set"  -- {* accessible part *}

inductive "acc r"
  intros
    accI [rule_format]:
      "\<forall>y. (y, x) \<in> r --> y \<in> acc r ==> x \<in> acc r"

syntax
  termi :: "('a \<times> 'a) set => 'a set"
translations
  "termi r" == "acc (r^-1)"


theorem acc_induct:
  "[| a \<in> acc r;
      !!x. [| x \<in> acc r;  \<forall>y. (y, x) \<in> r --> P y |] ==> P x
  |] ==> P a"
proof -
  assume major: "a \<in> acc r"
  assume hyp: "!!x. [| x \<in> acc r;  \<forall>y. (y, x) \<in> r --> P y |] ==> P x"
  show ?thesis
    apply (rule major [THEN acc.induct])
    apply (rule hyp)
     apply (rule accI)
     apply fast
    apply fast
    done
qed

theorem acc_downward: "[| b \<in> acc r; (a, b) \<in> r |] ==> a \<in> acc r"
  apply (erule acc.elims)
  apply fast
  done

lemma acc_downwards_aux: "(b, a) \<in> r^* ==> a \<in> acc r --> b \<in> acc r"
  apply (erule rtrancl_induct)
   apply blast
  apply (blast dest: acc_downward)
  done

theorem acc_downwards: "[| a \<in> acc r; (b, a) \<in> r^* |] ==> b \<in> acc r"
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
