(*  Title:      HOL/Lex/AutoMaxChop.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

goal thy "delta A (xs@[y]) q = next A y (delta A xs q)";
by(Simp_tac 1);
qed "delta_snoc";

goal thy
 "!q ps res. auto_split A (delta A ps q) ps xs res = \
\            maxsplit (%ys. fin A (delta A ys q)) ps xs res";
by(induct_tac "xs" 1);
by(Simp_tac 1);
by(asm_simp_tac (simpset() addsimps [delta_snoc RS sym]
                           delsimps [delta_append]) 1);
qed_spec_mp "auto_split_lemma";

goalw thy [accepts_def]
 "auto_split A (start A) [] xs res = maxsplit (accepts A) [] xs res";
by(stac ((read_instantiate [("s","start A")] delta_Nil) RS sym) 1);
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
