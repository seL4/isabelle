(*  Title:      HOL/Lex/Automata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

(*** Equivalence of NA and DA ***)

Goalw [na2da_def]
 "!Q. DA.delta (na2da A) w Q = Union(NA.delta A w `` Q)";
by (induct_tac "w" 1);
 by Auto_tac;
qed_spec_mp "DA_delta_is_lift_NA_delta";

Goalw [DA.accepts_def,NA.accepts_def]
  "NA.accepts A w = DA.accepts (na2da A) w";
by (simp_tac (simpset() addsimps [DA_delta_is_lift_NA_delta]) 1);
by (simp_tac (simpset() addsimps [na2da_def]) 1);
qed "NA_DA_equiv";

(*** Direct equivalence of NAe and DA ***)

Goalw [nae2da_def]
 "!Q. (eps A)^* ``` (DA.delta (nae2da A) w Q) = steps A w ``` Q";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [step_def]) 1);
by (Blast_tac 1);
qed_spec_mp "espclosure_DA_delta_is_steps";

Goalw [nae2da_def]
 "fin (nae2da A) Q = (? q : (eps A)^* ``` Q. fin A q)";
by (Simp_tac 1);
val lemma = result();

Goalw [NAe.accepts_def,DA.accepts_def]
  "DA.accepts (nae2da A) w = NAe.accepts A w";
by (simp_tac (simpset() addsimps [lemma,espclosure_DA_delta_is_steps]) 1);
by (simp_tac (simpset() addsimps [nae2da_def]) 1);
by (Blast_tac 1);
qed "NAe_DA_equiv";
