(*  Title:      HOL/Lex/NA.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Goal
 "steps A (v@w) = steps A w  O  steps A v";
by (induct_tac "v" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [O_assoc])));
qed "steps_append";
Addsimps [steps_append];

Goal "(p,r) : steps A (v@w) = ((p,r) : (steps A w O steps A v))";
by (rtac (steps_append RS equalityE) 1);
by (Blast_tac 1);
qed "in_steps_append";
AddIffs [in_steps_append];

Goal
 "!p. delta A w p = {q. (p,q) : steps A w}";
by (induct_tac "w" 1);
by (auto_tac (claset(), simpset() addsimps [step_def]));
qed_spec_mp "delta_conv_steps";

Goalw [accepts_def]
 "accepts A w = (? q. (start A,q) : steps A w & fin A q)";
by (simp_tac (simpset() addsimps [delta_conv_steps]) 1);
qed "accepts_conv_steps";
