(*  Title:      HOL/Lambda/ListOrder.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

Goalw [step1_def] "step1(r^-1) = (step1 r)^-1";
by (Blast_tac 1);
qed "step1_converse";
Addsimps [step1_converse];

Goal "(p : step1(r^-1)) = (p : (step1 r)^-1)";
by (Auto_tac);
qed "in_step1_converse";
AddIffs [in_step1_converse];

Goalw [step1_def] "([],xs) ~: step1 r";
by (Blast_tac 1);
qed "not_Nil_step1";
AddIffs [not_Nil_step1];

Goalw [step1_def] "(xs,[]) ~: step1 r";
by (Blast_tac 1);
qed "not_step1_Nil";
AddIffs [not_step1_Nil];

Goalw [step1_def]
  "((y#ys,x#xs) : step1 r) = ((y,x):r & xs=ys | x=y & (ys,xs) : step1 r)";
by (Asm_full_simp_tac 1);
by (rtac iffI 1);
 by (etac exE 1);
 by (rename_tac "ts" 1);
 by (case_tac "ts" 1);
  by (Force_tac 1);
 by (Force_tac 1);
by (etac disjE 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [Cons_eq_appendI]) 1);
qed "Cons_step1_Cons";
AddIffs [Cons_step1_Cons];

Goalw [step1_def]
 "(ys,xs) : step1 r & vs=us | ys=xs & (vs,us) : step1 r \
\ ==> (ys@vs,xs@us) : step1 r";
by (Auto_tac);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [append_eq_appendI]) 1);
qed "append_step1I";

Goal "[| (ys,x#xs) : step1 r; \
\        !y. ys = y#xs --> (y,x) : r --> R; \
\        !zs. ys = x#zs --> (zs,xs) : step1 r --> R \
\     |] ==> R";
by (case_tac "ys" 1);
 by (asm_full_simp_tac (simpset() addsimps [step1_def]) 1);
by (Blast_tac 1);
val lemma = result();
bind_thm("Cons_step1E",
          impI RSN (3,impI RSN (3,allI RSN (3,impI RSN (2,
          impI RSN (2,allI RSN (2,lemma)))))));
AddSEs [Cons_step1E];

Goalw [step1_def]
 "(ys@[y],xs@[x]) : step1 r ==> ((ys,xs) : step1 r & y=x | ys=xs & (y,x) : r)";
by (Asm_full_simp_tac 1);
by (clarify_tac (claset() delrules [disjCI]) 1);
by (rename_tac "vs" 1);
by (res_inst_tac [("xs","vs")]rev_exhaust 1);
 by (Force_tac 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "Snoc_step1_SnocD";

Goal "x : acc r ==> !xs. xs : acc(step1 r) --> x#xs : acc(step1 r)";
by (etac acc_induct 1);
by (etac thin_rl 1);
by (Clarify_tac 1);
by (etac acc_induct 1);
by (rtac accI 1);
by (Blast_tac 1);
val lemma = result();
qed_spec_mp "Cons_acc_step1I";
AddSIs [Cons_acc_step1I];

Goal "xs : lists(acc r) ==> xs : acc(step1 r)";
by (etac lists.induct 1);
 by (rtac accI 1);
 by (asm_full_simp_tac (simpset() addsimps [step1_def]) 1);
by (rtac accI 1);
by (fast_tac (claset() addDs [acc_downward]) 1);
qed "lists_accD";

Goalw [step1_def]
 "[| x : set xs; (y,x) : r |] ==> ? ys. (ys,xs) : step1 r & y : set ys";
by (dtac (in_set_conv_decomp RS iffD1) 1);
by (Force_tac 1);
qed "ex_step1I";

Goal "xs : acc(step1 r) ==> xs : lists(acc r)";
by (etac acc_induct 1);
by (Clarify_tac 1);
by (rtac accI 1);
by (EVERY1[dtac ex_step1I, atac]);
by (Blast_tac 1);
qed "lists_accI";
