(* Authors: Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow *)

header "Denotational Semantics of Commands"

theory Denotation imports Big_Step begin

type_synonym com_den = "(state \<times> state) set"

definition
  Gamma :: "bexp \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
  "Gamma b cd = (\<lambda>phi. {(s,t). (s,t) \<in> (cd O phi) \<and> bval b s} \<union>
                       {(s,t). s=t \<and> \<not>bval b s})"

fun C :: "com \<Rightarrow> com_den" where
"C SKIP   = Id" |
"C (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"C (c0;c1)   = C(c0) O C(c1)" |
"C (IF b THEN c1 ELSE c2) = {(s,t). (s,t) \<in> C c1 \<and> bval b s} \<union>
                            {(s,t). (s,t) \<in> C c2 \<and> \<not>bval b s}" |
"C(WHILE b DO c) = lfp (Gamma b (C c))"


lemma Gamma_mono: "mono (Gamma b c)"
by (unfold Gamma_def mono_def) fast

lemma C_While_If: "C(WHILE b DO c) = C(IF b THEN c;WHILE b DO c ELSE SKIP)"
apply simp
apply (subst lfp_unfold [OF Gamma_mono])  --{*lhs only*}
apply (simp add: Gamma_def)
done

text{* Equivalence of denotational and big-step semantics: *}

lemma com1: "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> C(c)"
apply (induction rule: big_step_induct)
apply auto
(* while *)
apply (unfold Gamma_def)
apply (subst lfp_unfold[OF Gamma_mono, simplified Gamma_def])
apply fast
apply (subst lfp_unfold[OF Gamma_mono, simplified Gamma_def])
apply auto 
done

lemma com2: "(s,t) \<in> C(c) \<Longrightarrow> (c,s) \<Rightarrow> t"
apply (induction c arbitrary: s t)
apply auto 
apply blast
(* while *)
apply (erule lfp_induct2 [OF _ Gamma_mono])
apply (unfold Gamma_def)
apply auto
done

lemma denotational_is_big_step: "(s,t) \<in> C(c)  =  ((c,s) \<Rightarrow> t)"
by (fast elim: com2 dest: com1)

end
