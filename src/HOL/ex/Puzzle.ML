(*  Title:      HOL/ex/puzzle.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993 TU Muenchen

A question from "Bundeswettbewerb Mathematik"

Proof due to Herbert Ehler
*)

AddSIs [Puzzle.f_ax];

Goal "! n. k=f(n) --> n <= f(n)";
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac allI 1);
by (rename_tac "i" 1);
by (cases_tac "i" 1);
 by (Asm_simp_tac 1);
by (blast_tac (claset() addSIs [Suc_leI] addIs [le_less_trans]) 1);
val lemma = result() RS spec RS mp;

Goal "n <= f(n)";
by (fast_tac (claset() addIs [lemma]) 1);
qed "lemma1";

Goal "f(n) < f(Suc(n))";
by (blast_tac (claset() addIs [le_less_trans, lemma1]) 1);
qed "lemma2";

Goal "m <= n --> f(m) <= f(n)";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (rtac impI 1);
by (etac le_SucE 1);
 by(cut_inst_tac [("n","n")]lemma2 1);
 by(arith_tac 1);
by(Asm_simp_tac 1);
qed_spec_mp "f_mono";

Goal "f(n) = n";
by (rtac order_antisym 1);
by (rtac lemma1 2);
by (fast_tac (claset() addIs [leI] addDs [leD,f_mono,Suc_leI]) 1);
qed "f_id";
