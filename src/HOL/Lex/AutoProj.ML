(*  Title:      HOL/Lex/AutoProj.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

goalw thy [start_def] "start(q,d,f) = q";
by(Simp_tac 1);
qed "start_conv";

goalw thy [next_def] "next(q,d,f) = d";
by(Simp_tac 1);
qed "next_conv";

goalw thy [fin_def] "fin(q,d,f) = f";
by(Simp_tac 1);
qed "fin_conv";

Addsimps [start_conv,next_conv,fin_conv];
