(*  Title:      ZF/Induct/Acc.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>The accessible part of a relation\<close>

theory Acc imports ZF begin

text \<open>
  Inductive definition of \<open>acc(r)\<close>; see @{cite "paulin-tlca"}.
\<close>

consts
  acc :: "i => i"

inductive
  domains "acc(r)" \<subseteq> "field(r)"
  intros
    vimage:  "\<lbrakk>r-``{a}: Pow(acc(r)); a \<in> field(r)\<rbrakk> \<Longrightarrow> a \<in> acc(r)"
  monos      Pow_mono

text \<open>
  The introduction rule must require \<^prop>\<open>a \<in> field(r)\<close>,
  otherwise \<open>acc(r)\<close> would be a proper class!

  \medskip
  The intended introduction rule:
\<close>

lemma accI: "\<lbrakk>\<And>b. <b,a>:r \<Longrightarrow> b \<in> acc(r);  a \<in> field(r)\<rbrakk> \<Longrightarrow> a \<in> acc(r)"
  by (blast intro: acc.intros)

lemma acc_downward: "\<lbrakk>b \<in> acc(r);  <a,b>: r\<rbrakk> \<Longrightarrow> a \<in> acc(r)"
  by (erule acc.cases) blast

lemma acc_induct [consumes 1, case_names vimage, induct set: acc]:
    "\<lbrakk>a \<in> acc(r);
        \<And>x. \<lbrakk>x \<in> acc(r);  \<forall>y. <y,x>:r \<longrightarrow> P(y)\<rbrakk> \<Longrightarrow> P(x)
\<rbrakk> \<Longrightarrow> P(a)"
  by (erule acc.induct) (blast intro: acc.intros)

lemma wf_on_acc: "wf[acc(r)](r)"
  apply (rule wf_onI2)
  apply (erule acc_induct)
  apply fast
  done

lemma acc_wfI: "field(r) \<subseteq> acc(r) \<Longrightarrow> wf(r)"
  by (erule wf_on_acc [THEN wf_on_subset_A, THEN wf_on_field_imp_wf])

lemma acc_wfD: "wf(r) \<Longrightarrow> field(r) \<subseteq> acc(r)"
  apply (rule subsetI)
  apply (erule wf_induct2, assumption)
   apply (blast intro: accI)+
  done

lemma wf_acc_iff: "wf(r) \<longleftrightarrow> field(r) \<subseteq> acc(r)"
  by (rule iffI, erule acc_wfD, erule acc_wfI)

end
