(*
    Factorisation within a factorial domain
    $Id$
    Author: Clemens Ballarin, started 25 November 1997
*)

Goalw [thm "assoc_def"] "!! c::'a::factorial. \
\  [| irred c; irred a; irred b; c dvd a*b |] ==> c assoc a | c assoc b";
by (ftac (thm "factorial_prime") 1);
by (rewrite_goals_tac [thm "irred_def", thm "prime_def"]);
by (Blast_tac 1);
qed "irred_dvd_lemma";

Goalw [thm "assoc_def"] "!! c::'a::factorial. \
\  [| irred c; a dvd 1 |] ==> \
\  (ALL b : set factors. irred b) & c dvd foldr op* factors a --> \
\  (EX d. c assoc d & d : set factors)";
by (induct_tac "factors" 1);
(* Base case: c dvd a contradicts irred c *)
by (full_simp_tac (simpset() addsimps [thm "irred_def"]) 1);
by (blast_tac (claset() addIs [dvd_trans_ring]) 1);
(* Induction step *)
by (ftac (thm "factorial_prime") 1);
by (full_simp_tac (simpset() addsimps [thm "irred_def", thm "prime_def"]) 1);
by (Blast_tac 1);
qed "irred_dvd_list_lemma";

Goal "!! c::'a::factorial. \
\  [| irred c; ALL b : set factors. irred b; a dvd 1; \
\    c dvd foldr op* factors a |] ==> \
\  EX d. c assoc d & d : set factors";
by (rtac (irred_dvd_list_lemma RS mp) 1);
by (Auto_tac);
qed "irred_dvd_list";

Goalw [Factorisation_def] "!! c::'a::factorial. \
\  [| irred c; Factorisation x factors u; c dvd x |] ==> \
\  EX d. c assoc d & d : set factors";
by (rtac (irred_dvd_list_lemma RS mp) 1);
by (Auto_tac);
qed "Factorisation_dvd";

Goalw [Factorisation_def] "!! c::'a::factorial. \
\  [| Factorisation x factors u; a : set factors |] ==> irred a";
by (Blast_tac 1);
qed "Factorisation_irred";

