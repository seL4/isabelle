(*  Title:      HOL/ex/puzzle.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993 TU Muenchen

For puzzle.thy.  A question from "Bundeswettbewerb Mathematik"

Proof due to Herbert Ehler
*)

(*specialized form of induction needed below*)
val prems = goal Nat.thy "[| P(0); !!n. P(Suc(n)) |] ==> !n.P(n)";
by (EVERY1 [rtac (nat_induct RS allI), resolve_tac prems, resolve_tac prems]);
qed "nat_exh";

goal Puzzle.thy "! n. k=f(n) --> n <= f(n)";
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac nat_exh 1);
by (Simp_tac 1);
by (rtac impI 1);
by (rtac classical 1);
by (dtac not_leE 1);
by (subgoal_tac "f(na) <= f(f(na))" 1);
by (fast_tac (!claset addIs [Puzzle.f_ax]) 2);
by (rtac lessD 1);
by (best_tac (!claset delrules [le_refl] 
                      addIs [Puzzle.f_ax, le_less_trans]) 1);
val lemma = result() RS spec RS mp;

goal Puzzle.thy "n <= f(n)";
by (fast_tac (!claset addIs [lemma]) 1);
qed "lemma1";

goal Puzzle.thy "f(n) < f(Suc(n))";
by (deepen_tac (!claset addIs [Puzzle.f_ax, le_less_trans, lemma1]) 0 1);
qed "lemma2";

val prems = goal Puzzle.thy "(!!n.f(n) <= f(Suc(n))) ==> m<n --> f(m) <= f(n)";
by (res_inst_tac[("n","n")]nat_induct 1);
by (Simp_tac 1);
by (simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (best_tac (!claset addIs (le_trans::prems)) 1);
qed_spec_mp "mono_lemma1";

val [p1,p2] = goal Puzzle.thy
    "[| !! n. f(n)<=f(Suc(n));  m<=n |] ==> f(m) <= f(n)";
by (rtac (p2 RS le_imp_less_or_eq RS disjE) 1);
by (etac (p1 RS mono_lemma1) 1);
by (Fast_tac 1);
qed "mono_lemma";

val prems = goal Puzzle.thy "m <= n ==> f(m) <= f(n)";
by (fast_tac (!claset addIs ([mono_lemma,less_imp_le,lemma2]@prems)) 1);
qed "f_mono";

goal Puzzle.thy "f(n) = n";
by (rtac le_anti_sym 1);
by (rtac lemma1 2);
by (fast_tac (!claset addIs [Puzzle.f_ax,leI] addDs [leD,f_mono,lessD]) 1);
result();
