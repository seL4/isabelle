(*  Title:      HOL/ex/puzzle.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993 TU Muenchen

A question from "Bundeswettbewerb Mathematik"

Proof due to Herbert Ehler
*)

AddSIs [Puzzle.f_ax];

(*specialized form of induction needed below*)
val prems = goal Nat.thy "[| P(0); !!n. P(Suc(n)) |] ==> !n. P(n)";
by (EVERY1 [rtac (nat_induct RS allI), resolve_tac prems, resolve_tac prems]);
qed "nat_exh";

Goal "! n. k=f(n) --> n <= f(n)";
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac nat_exh 1);
by (Simp_tac 1);
by (rtac impI 1);
by (rtac classical 1);
by (dtac not_leE 1);
by (subgoal_tac "f(na) <= f(f(na))" 1);
by (Blast_tac 2);
by (rtac Suc_leI 1);
by (blast_tac (claset() addSDs [spec] addIs [le_less_trans]) 1);
val lemma = result() RS spec RS mp;

Goal "n <= f(n)";
by (fast_tac (claset() addIs [lemma]) 1);
qed "lemma1";

Goal "f(n) < f(Suc(n))";
by (blast_tac (claset() addIs [le_less_trans, lemma1]) 1);
qed "lemma2";

val prems = Goal "(!!n. f(n) <= f(Suc(n))) ==> m<n --> f(m) <= f(n)";
by (res_inst_tac[("n","n")]nat_induct 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (blast_tac (claset() addIs (le_trans::prems)) 1);
qed_spec_mp "mono_lemma1";

val [p1,p2] = goal Puzzle.thy
    "[| !! n. f(n)<=f(Suc(n));  m<=n |] ==> f(m) <= f(n)";
by (rtac (p2 RS le_imp_less_or_eq RS disjE) 1);
by (etac (p1 RS mono_lemma1) 1);
by (Fast_tac 1);
qed "mono_lemma";

val prems = goal Puzzle.thy "m <= n ==> f(m) <= f(n)";
by (fast_tac (claset() addIs [mono_lemma,less_imp_le,lemma2]@prems) 1);
qed "f_mono";

Goal "f(n) = n";
by (rtac order_antisym 1);
by (rtac lemma1 2);
by (fast_tac (claset() addIs [Puzzle.f_ax,leI] addDs [leD,f_mono,Suc_leI]) 1);
result();
