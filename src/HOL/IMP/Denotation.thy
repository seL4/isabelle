(*  Title:      HOL/IMP/Denotation.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

header "Denotational Semantics of Commands"

theory Denotation = Natural:

types com_den = "(state\<times>state)set"

constdefs
  Gamma :: "[bexp,com_den] => (com_den => com_den)"
  "Gamma b cd == (\<lambda>phi. {(s,t). (s,t) \<in> (phi O cd) \<and> b s} \<union> 
                       {(s,t). s=t \<and> \<not>b s})"
    
consts
  C :: "com => com_den"

primrec
  C_skip:   "C \<SKIP>   = Id"
  C_assign: "C (x :== a) = {(s,t). t = s[x\<mapsto>a(s)]}"
  C_comp:   "C (c0;c1)   = C(c1) O C(c0)"
  C_if:     "C (\<IF> b \<THEN> c1 \<ELSE> c2) = {(s,t). (s,t) \<in> C c1 \<and> b s} \<union>
                                                {(s,t). (s,t) \<in> C c2 \<and> \<not>b s}"
  C_while:  "C(\<WHILE> b \<DO> c) = lfp (Gamma b (C c))"


(**** mono (Gamma(b,c)) ****)

lemma Gamma_mono: "mono (Gamma b c)"
  by (unfold Gamma_def mono_def) fast

lemma C_While_If: "C(\<WHILE> b \<DO> c) = C(\<IF> b \<THEN> c;\<WHILE> b \<DO> c \<ELSE> \<SKIP>)"
apply (simp (no_asm)) 
apply (subst lfp_unfold [OF Gamma_mono]) back back
apply (subst Gamma_def [THEN meta_eq_to_obj_eq, THEN fun_cong]) 
apply simp
done

(* Operational Semantics implies Denotational Semantics *)

lemma com1: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t \<Longrightarrow> (s,t) \<in> C(c)"

(* start with rule induction *)
apply (erule evalc.induct)
apply auto
(* while *)
apply (unfold Gamma_def)
apply (subst lfp_unfold[OF Gamma_mono, simplified Gamma_def])
apply fast
apply (subst lfp_unfold[OF Gamma_mono, simplified Gamma_def])
apply fast
done

(* Denotational Semantics implies Operational Semantics *)

lemma com2 [rule_format]: "\<forall>s t. (s,t)\<in>C(c) \<longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
apply (induct_tac "c")

apply (simp_all (no_asm_use))
apply fast
apply fast

(* while *)
apply (intro strip)
apply (erule lfp_induct [OF _ Gamma_mono])
apply (unfold Gamma_def)
apply fast
done


(**** Proof of Equivalence ****)

lemma denotational_is_natural: "(s,t) \<in> C(c)  =  (\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t)"
apply (fast elim: com2 dest: com1)
done

end
