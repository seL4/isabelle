(*  Title:      HOLCF/IMP/HoareEx.thy
    ID:         $Id$
    Author:     Tobias Nipkow, TUM
    Copyright   1997 TUM
*)

header "Correctness of Hoare by Fixpoint Reasoning"

theory HoareEx = Denotational:

text {*
  An example from the HOLCF paper by Müller, Nipkow, Oheimb, Slotosch
  \cite{MuellerNvOS99}.  It demonstrates fixpoint reasoning by showing
  the correctness of the Hoare rule for while-loops.
*}

types assn = "state => bool"

constdefs
  hoare_valid :: "[assn, com, assn] => bool"    ("|= {(1_)}/ (_)/ {(1_)}" 50)
  "|= {A} c {B} == \<forall>s t. A s \<and> D c $(Discr s) = Def t --> B t"

lemma WHILE_rule_sound:
    "|= {A} c {A} ==> |= {A} \<WHILE> b \<DO> c {\<lambda>s. A s \<and> \<not> b s}"
  apply (unfold hoare_valid_def)
  apply (simp (no_asm))
  apply (rule fix_ind)
    apply (simp (no_asm)) -- "simplifier with enhanced @{text adm}-tactic"
   apply (simp (no_asm))
  apply (simp (no_asm))
  apply blast
  done

end
