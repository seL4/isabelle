(*  Title:      HOL/Lex/AutoMaxChop.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

goal thy "!q ys. nexts A q (xs@ys) = nexts A (nexts A q xs) ys";
by(induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "nexts_append";
Addsimps [nexts_append];

goal thy "nexts A q (xs@[y]) = next A (nexts A q xs) y";
by(Simp_tac 1);
qed "nexts_snoc";
Addsimps [nexts_append];

goal thy
 "!q ps res. auto_split A (nexts A q ps) ps xs res = \
\            maxsplit (%ys. fin A (nexts A q ys)) ps xs res";
by(induct_tac "xs" 1);
by(Simp_tac 1);
by(asm_simp_tac (simpset() addsimps [nexts_snoc RS sym]
                           delsimps [nexts_append]) 1);
qed_spec_mp "auto_split_lemma";

goalw thy [accepts_def]
 "auto_split A (start A) [] xs res = maxsplit (accepts A) [] xs res";
by(stac ((read_instantiate [("st","start A")] nexts_Nil) RS sym) 1);
by(stac auto_split_lemma 1);
by(Simp_tac 1);
qed_spec_mp "auto_split_is_maxsplit";

goal thy
 "is_maxsplitter (accepts A) (%xs. auto_split A (start A) [] xs ([],xs))";
by(simp_tac (simpset() addsimps
        [auto_split_is_maxsplit,is_maxsplitter_maxsplit]) 1);
qed "is_maxsplitter_auto_split";

goalw thy [auto_chop_def]
 "is_maxchopper (accepts A) (auto_chop A)";
br is_maxchopper_chop 1;
br is_maxsplitter_auto_split 1;
qed "is_maxchopper_auto_chop";
