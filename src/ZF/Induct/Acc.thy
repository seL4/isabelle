(*  Title:      ZF/Induct/Acc.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of acc(r)

See Ch. Paulin-Mohring, Inductive Definitions in the System Coq.
Research Report 92-49, LIP, ENS Lyon.  Dec 1992.
*)

theory Acc = Main:

consts
  acc :: "i=>i"

inductive
  domains "acc(r)" <= "field(r)"
  intros
    vimage:  "[| r-``{a}: Pow(acc(r)); a \<in> field(r) |] ==> a \<in> acc(r)"
  monos      Pow_mono


(*The introduction rule must require  a \<in> field(r)  
  Otherwise acc(r) would be a proper class!    *)

(*The intended introduction rule*)
lemma accI: "[| !!b. <b,a>:r ==> b \<in> acc(r);  a \<in> field(r) |] ==> a \<in> acc(r)"
by (blast intro: acc.intros)

lemma acc_downward: "[| b \<in> acc(r);  <a,b>: r |] ==> a \<in> acc(r)"
by (erule acc.cases, blast)

lemma acc_induct:
    "[| a \<in> acc(r);                                              
        !!x. [| x \<in> acc(r);  \<forall>y. <y,x>:r --> P(y) |] ==> P(x)  
     |] ==> P(a)"
apply (erule acc.induct)
apply (blast intro: acc.intros) 
done

lemma wf_on_acc: "wf[acc(r)](r)"
apply (rule wf_onI2)
apply (erule acc_induct)
apply fast
done

(* field(r) \<subseteq> acc(r) ==> wf(r) *)
lemmas acc_wfI = wf_on_acc [THEN wf_on_subset_A, THEN wf_on_field_imp_wf]

lemma acc_wfD: "wf(r) ==> field(r) \<subseteq> acc(r)"
apply (rule subsetI)
apply (erule wf_induct2, assumption)
apply (blast intro: accI)+
done

lemma wf_acc_iff: "wf(r) <-> field(r) \<subseteq> acc(r)"
by (rule iffI, erule acc_wfD, erule acc_wfI) 

end
