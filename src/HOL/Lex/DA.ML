(*  Title:      HOL/Lex/DA.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

goalw thy [foldl2_def] "foldl2 f [] a = a";
by(Simp_tac 1);
qed "foldl2_Nil";

goalw thy [foldl2_def] "foldl2 f (x#xs) a = foldl2 f xs (f x a)";
by(Simp_tac 1);
qed "foldl2_Cons";

Addsimps [foldl2_Nil,foldl2_Cons];

goalw thy [delta_def] "delta A [] s = s";
by(Simp_tac 1);
qed "delta_Nil";

goalw thy [delta_def] "delta A (a#w) s = delta A w (next A a s)";
by(Simp_tac 1);
qed "delta_Cons";

Addsimps [delta_Nil,delta_Cons];

goal thy "!q ys. delta A (xs@ys) q = delta A ys (delta A xs q)";
by(induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "delta_append";
Addsimps [delta_append];
