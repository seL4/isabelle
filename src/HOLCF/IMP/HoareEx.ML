(*  Title:      HOLCF/IMP/HoareEx.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TUM

Correctness of while-loop.
*)

val prems = goalw thy [hoare_valid_def]
"|= {A} c {A} ==> |= {A} WHILE b DO c {%s. A s & ~b s}";
by (cut_facts_tac prems 1);
by (Simp_tac 1);
by (rtac fix_ind 1);
  (* simplifier with enhanced adm-tactic: *)
  by (Simp_tac 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Blast_tac 1);
qed "WHILE_rule_sound";
