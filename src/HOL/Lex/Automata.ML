(*  Title:      HOL/Lex/Automata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

(*** Equivalence of NA and DA --- redundant ***)

goalw thy [na2da_def]
 "!Q. DA.delta (na2da A) w Q = Union(NA.delta A w `` Q)";
by(induct_tac "w" 1);
 by(ALLGOALS Asm_simp_tac);
 by(ALLGOALS Blast_tac);
qed_spec_mp "DA_delta_is_lift_NA_delta";

goalw thy [DA.accepts_def,NA.accepts_def]
  "NA.accepts A w = DA.accepts (na2da A) w";
by(simp_tac (simpset() addsimps [DA_delta_is_lift_NA_delta]) 1);
by(simp_tac (simpset() addsimps [na2da_def]) 1);
qed "NA_DA_equiv";

(*** Direct equivalence of NAe and DA ***)

goalw thy [nae2da_def]
 "!Q. (eps A)^* ^^ (DA.delta (nae2da A) w Q) = steps A w ^^ Q";
by(induct_tac "w" 1);
 by (Simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [step_def]) 1);
by(Blast_tac 1);
qed_spec_mp "espclosure_DA_delta_is_steps";

goalw thy [nae2da_def]
 "fin (nae2da A) Q = (? q : (eps A)^* ^^ Q. fin A q)";
by(Simp_tac 1);
val lemma = result();

goalw thy [NAe.accepts_def,DA.accepts_def]
  "DA.accepts (nae2da A) w = NAe.accepts A w";
by(simp_tac (simpset() addsimps [lemma,espclosure_DA_delta_is_steps]) 1);
by(simp_tac (simpset() addsimps [nae2da_def]) 1);
by(Blast_tac 1);
qed "NAe_DA_equiv";
