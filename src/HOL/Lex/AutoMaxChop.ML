(*  Title:      HOL/Lex/AutoMaxChop.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Goal "delta A (xs@[y]) q = next A y (delta A xs q)";
by (Simp_tac 1);
qed "delta_snoc";

Goal
 "!q ps res. auto_split A (delta A ps q) res ps xs = \
\            maxsplit (%ys. fin A (delta A ys q)) res ps xs";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [delta_snoc RS sym]
                           delsimps [thm"delta_append"]) 1);
qed_spec_mp "auto_split_lemma";

Goalw [thm"accepts_def"]
 "auto_split A (start A) res [] xs = maxsplit (accepts A) res [] xs";
by (stac ((read_instantiate [("s","start A")] (thm"delta_Nil")) RS sym) 1);
by (stac auto_split_lemma 1);
by (Simp_tac 1);
qed_spec_mp "auto_split_is_maxsplit";

Goal
 "is_maxsplitter (accepts A) (%xs. auto_split A (start A) ([],xs) [] xs)";
by (simp_tac (simpset() addsimps
        [auto_split_is_maxsplit,thm"is_maxsplitter_maxsplit"]) 1);
qed "is_maxsplitter_auto_split";

Goalw [thm"auto_chop_def"]
 "is_maxchopper (accepts A) (auto_chop A)";
by (rtac (thm"is_maxchopper_chop") 1);
by (rtac is_maxsplitter_auto_split 1);
qed "is_maxchopper_auto_chop";
