(*  Title:      HOL/IMP/Denotation.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

header "Denotational Semantics of Commands"

theory Denotation imports Natural begin

types com_den = "(state\<times>state)set"

definition
  Gamma :: "[bexp,com_den] => (com_den => com_den)" where
  "Gamma b cd = (\<lambda>phi. {(s,t). (s,t) \<in> (cd O phi) \<and> b s} \<union>
                       {(s,t). s=t \<and> \<not>b s})"

primrec C :: "com => com_den"
where
  C_skip:   "C \<SKIP>   = Id"
| C_assign: "C (x :== a) = {(s,t). t = s[x\<mapsto>a(s)]}"
| C_comp:   "C (c0;c1)   = C(c0) O C(c1)"
| C_if:     "C (\<IF> b \<THEN> c1 \<ELSE> c2) = {(s,t). (s,t) \<in> C c1 \<and> b s} \<union>
                                                {(s,t). (s,t) \<in> C c2 \<and> \<not>b s}"
| C_while:  "C(\<WHILE> b \<DO> c) = lfp (Gamma b (C c))"


(**** mono (Gamma(b,c)) ****)

lemma Gamma_mono: "mono (Gamma b c)"
  by (unfold Gamma_def mono_def) fast

lemma C_While_If: "C(\<WHILE> b \<DO> c) = C(\<IF> b \<THEN> c;\<WHILE> b \<DO> c \<ELSE> \<SKIP>)"
apply simp
apply (subst lfp_unfold [OF Gamma_mono])  --{*lhs only*}
apply (simp add: Gamma_def)
done

(* Operational Semantics implies Denotational Semantics *)

lemma com1: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t \<Longrightarrow> (s,t) \<in> C(c)"
(* start with rule induction *)
apply (induct set: evalc)
apply auto
(* while *)
apply (unfold Gamma_def)
apply (subst lfp_unfold[OF Gamma_mono, simplified Gamma_def])
apply fast
apply (subst lfp_unfold[OF Gamma_mono, simplified Gamma_def])
apply fast
done

(* Denotational Semantics implies Operational Semantics *)

lemma com2: "(s,t) \<in> C(c) \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
apply (induct c arbitrary: s t)

apply simp_all
apply fast
apply fast

(* while *)
apply (erule lfp_induct2 [OF _ Gamma_mono])
apply (unfold Gamma_def)
apply fast
done


(**** Proof of Equivalence ****)

lemma denotational_is_natural: "(s,t) \<in> C(c)  =  (\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t)"
  by (fast elim: com2 dest: com1)

end
