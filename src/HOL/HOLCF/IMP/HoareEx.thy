(*  Title:      HOL/HOLCF/IMP/HoareEx.thy
    Author:     Tobias Nipkow, TUM
    Copyright   1997 TUM
*)

section "Correctness of Hoare by Fixpoint Reasoning"

theory HoareEx imports Denotational begin

text \<open>
  An example from the HOLCF paper by Müller, Nipkow, Oheimb, Slotosch
  @{cite MuellerNvOS99}.  It demonstrates fixpoint reasoning by showing
  the correctness of the Hoare rule for while-loops.
\<close>

type_synonym assn = "state \<Rightarrow> bool"

definition
  hoare_valid :: "[assn, com, assn] \<Rightarrow> bool"  ("|= {(1_)}/ (_)/ {(1_)}" 50) where
  "|= {P} c {Q} = (\<forall>s t. P s \<and> D c\<cdot>(Discr s) = Def t \<longrightarrow> Q t)"

lemma WHILE_rule_sound:
    "|= {A} c {A} \<Longrightarrow> |= {A} WHILE b DO c {\<lambda>s. A s \<and> \<not> bval b s}"
  apply (unfold hoare_valid_def)
  apply (simp (no_asm))
  apply (rule fix_ind)
    apply (simp (no_asm)) \<comment> \<open>simplifier with enhanced \<open>adm\<close>-tactic\<close>
   apply (simp (no_asm))
  apply (simp (no_asm))
  apply blast
  done

end
