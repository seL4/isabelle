(*  Title:      HOL/Lex/NAe.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

goal thy
 "steps A w O (eps A)^* = steps A w";
by (exhaust_tac "w" 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [O_assoc])));
qed_spec_mp "steps_epsclosure";
Addsimps [steps_epsclosure];

goal thy
 "!! A. [| (p,q) : (eps A)^*; (q,r) : steps A w |] ==> (p,r) : steps A w";
by(rtac (steps_epsclosure RS equalityE) 1);
by(Blast_tac 1);
qed "in_steps_epsclosure";

goal thy "(eps A)^* O steps A w = steps A w";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [O_assoc RS sym]) 1);
qed "epsclosure_steps";

goal thy
 "!!A. [| (p,q) : steps A w; (q,r) : (eps A)^* |] ==> (p,r) : steps A w";
by(rtac (epsclosure_steps RS equalityE) 1);
by(Blast_tac 1);
qed "in_epsclosure_steps";

goal thy
 "steps A (v@w) = steps A w  O  steps A v";
by (induct_tac "v" 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [O_assoc])));
qed "steps_append";
Addsimps [steps_append];

goal thy "(p,r) : steps A (v@w) = ((p,r) : (steps A w O steps A v))";
by(rtac (steps_append RS equalityE) 1);
by(Blast_tac 1);
qed "in_steps_append";
AddIffs [in_steps_append];

(** Equivalence of steps and delta **)
(* Use "(? x : f `` A. P x) = (? a:A. P(f x))" ?? *)
goal thy "!p. (p,q) : steps A w = (q : delta A w p)";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [comp_def,step_def]) 1);
by(Blast_tac 1);
qed_spec_mp "steps_equiv_delta";
