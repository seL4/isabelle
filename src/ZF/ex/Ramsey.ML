(*  Title:      ZF/ex/ramsey.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ramsey's Theorem (finite exponent 2 version)

Based upon the article
    D Basin and M Kaufmann,
    The Boyer-Moore Prover and Nuprl: An Experimental Comparison.
    In G Huet and G Plotkin, editors, Logical Frameworks.
    (CUP, 1991), pages 89--119

See also
    M Kaufmann,
    An example in NQTHM: Ramsey's Theorem
    Internal Note, Computational Logic, Inc., Austin, Texas 78703
    Available from the author: kaufmann@cli.com
*)

(*** Cliques and Independent sets ***)

Goalw [Clique_def] "Clique(0,V,E)";
by (Fast_tac 1);
qed "Clique0";

Goalw [Clique_def] "[| Clique(C,V',E);  V'<=V |] ==> Clique(C,V,E)";
by (Fast_tac 1);
qed "Clique_superset";

Goalw [Indept_def] "Indept(0,V,E)";
by (Fast_tac 1);
qed "Indept0";

Goalw [Indept_def] "[| Indept(I,V',E);  V'<=V |] ==> Indept(I,V,E)";
by (Fast_tac 1);
qed "Indept_superset";

(*** Atleast ***)

Goalw [Atleast_def, inj_def, Pi_def, function_def] "Atleast(0,A)";
by (Fast_tac 1);
qed "Atleast0";

Goalw [Atleast_def]
    "Atleast(succ(m),A) ==> \\<exists>x \\<in> A. Atleast(m, A-{x})";
by (fast_tac (claset() addEs [inj_is_fun RS apply_type, inj_succ_restrict]) 1);
qed "Atleast_succD";

Goalw [Atleast_def]
    "[| Atleast(n,A);  A \\<subseteq> B |] ==> Atleast(n,B)";
by (fast_tac (claset() addEs [inj_weaken_type]) 1);
qed "Atleast_superset";

Goalw [Atleast_def,succ_def]
    "[| Atleast(m,B);  b\\<notin> B |] ==> Atleast(succ(m), cons(b,B))";
by (etac exE 1);
by (rtac exI 1);
by (etac inj_extend 1);
by (rtac mem_not_refl 1);
by (assume_tac 1);
qed "Atleast_succI";

Goal "[| Atleast(m, B-{x});  x \\<in> B |] ==> Atleast(succ(m), B)";
by (etac (Atleast_succI RS Atleast_superset) 1);
by (Fast_tac 1);
by (Fast_tac 1);
qed "Atleast_Diff_succI";

(*** Main Cardinality Lemma ***)

(*The #-succ(0) strengthens the original theorem statement, but precisely
  the same proof could be used!!*)
Goal "m \\<in> nat ==> \
\     \\<forall>n \\<in> nat. \\<forall>A B. Atleast((m#+n) #- succ(0), A Un B) -->   \
\                          Atleast(m,A) | Atleast(n,B)";
by (induct_tac "m" 1);
by (fast_tac (claset() addSIs [Atleast0]) 1);
by (Asm_simp_tac 1);
by (rtac ballI 1);
by (rename_tac "m' n" 1);       (*simplifier does NOT preserve bound names!*)
by (induct_tac "n" 1);
by (fast_tac (claset() addSIs [Atleast0]) 1);
by (Asm_simp_tac 1);
by Safe_tac;
by (etac (Atleast_succD RS bexE) 1);
by (rename_tac "n' A B z" 1);
by (etac UnE 1);
(**case z \\<in> B.  Instantiate the '\\<forall>A B' induction hypothesis. **)
by (dres_inst_tac [("x1","A"), ("x","B-{z}")] (spec RS spec) 2);
by (etac (mp RS disjE) 2);
(*cases Atleast(succ(m1),A) and Atleast(succ(k),B)*)
by (REPEAT (eresolve_tac [asm_rl, notE, Atleast_Diff_succI] 3));
(*proving the condition*)
by (etac Atleast_superset 2 THEN Fast_tac 2);
(**case z \\<in> A.  Instantiate the '\\<forall>n \\<in> nat. \\<forall>A B' induction hypothesis. **)
by (dres_inst_tac [("x2","succ(n')"), ("x1","A-{z}"), ("x","B")] 
    (bspec RS spec RS spec) 1);
by (etac nat_succI 1);
by (etac (mp RS disjE) 1);
(*cases Atleast(succ(m1),A) and Atleast(succ(k),B)*)
by (REPEAT (eresolve_tac [asm_rl, Atleast_Diff_succI, notE] 2));
(*proving the condition*)
by (Asm_simp_tac 1);
by (etac Atleast_superset 1 THEN Fast_tac 1);
qed_spec_mp "pigeon2";


(**** Ramsey's Theorem ****)

(** Base cases of induction; they now admit ANY Ramsey number **)

Goalw [Ramsey_def] "Ramsey(n,0,j)";
by (fast_tac (claset() addIs [Clique0,Atleast0]) 1);
qed "Ramsey0j";

Goalw [Ramsey_def] "Ramsey(n,i,0)";
by (fast_tac (claset() addIs [Indept0,Atleast0]) 1);
qed "Ramseyi0";

(** Lemmas for induction step **)

(*The use of succ(m) here, rather than #-succ(0), simplifies the proof of 
  Ramsey_step_lemma.*)
Goal "[| Atleast(m #+ n, A);  m \\<in> nat;  n \\<in> nat |]  \
\     ==> Atleast(succ(m), {x \\<in> A. ~P(x)}) | Atleast(n, {x \\<in> A. P(x)})";
by (rtac (nat_succI RS pigeon2) 1);
by (Asm_simp_tac 3);
by (rtac Atleast_superset 3);
by Auto_tac;
qed "Atleast_partition";

(*For the Atleast part, proves ~(a \\<in> I) from the second premise!*)
Goalw [Symmetric_def,Indept_def]
    "[| Symmetric(E);  Indept(I, {z \\<in> V-{a}. <a,z> \\<notin> E}, E);  a \\<in> V;  \
\       Atleast(j,I) |] ==>   \
\    Indept(cons(a,I), V, E) & Atleast(succ(j), cons(a,I))";
by (blast_tac (claset() addSIs [Atleast_succI]) 1);
qed "Indept_succ";

Goalw [Symmetric_def,Clique_def]
    "[| Symmetric(E);  Clique(C, {z \\<in> V-{a}. <a,z>:E}, E);  a \\<in> V;  \
\       Atleast(j,C) |] ==>   \
\    Clique(cons(a,C), V, E) & Atleast(succ(j), cons(a,C))";
by (blast_tac (claset() addSIs [Atleast_succI]) 1);
qed "Clique_succ";

(** Induction step **)

(*Published proofs gloss over the need for Ramsey numbers to be POSITIVE.*)
val ram1::ram2::prems = goalw Ramsey.thy [Ramsey_def] 
   "[| Ramsey(succ(m), succ(i), j);  Ramsey(n, i, succ(j));  \
\      m \\<in> nat;  n \\<in> nat |] ==> \
\   Ramsey(succ(m#+n), succ(i), succ(j))";
by Safe_tac;
by (etac (Atleast_succD RS bexE) 1);
by (eres_inst_tac [("P1","%z.<x,z>:E")] (Atleast_partition RS disjE) 1);
by (REPEAT (resolve_tac prems 1));
(*case m*)
by (rtac (ram1 RS spec RS spec RS mp RS disjE) 1);
by (Fast_tac 1);
by (fast_tac (claset() addEs [Clique_superset]) 1); (*easy -- given a Clique*)
by Safe_tac;
by (eresolve_tac (swapify [exI]) 1);             (*ignore main \\<exists>quantifier*)
by (REPEAT (ares_tac [Indept_succ] 1));          (*make a bigger Indept*)
(*case n*)
by (rtac (ram2 RS spec RS spec RS mp RS disjE) 1);
by (Fast_tac 1);
by Safe_tac;
by (rtac exI 1);
by (REPEAT (ares_tac [Clique_succ] 1));          (*make a bigger Clique*)
by (fast_tac (claset() addEs [Indept_superset]) 1); (*easy -- given an Indept*)
qed "Ramsey_step_lemma";


(** The actual proof **)

(*Again, the induction requires Ramsey numbers to be positive.*)
Goal "i \\<in> nat ==> \\<forall>j \\<in> nat. \\<exists>n \\<in> nat. Ramsey(succ(n), i, j)";
by (induct_tac "i" 1);
by (fast_tac (claset() addSIs [Ramsey0j]) 1);
by (rtac ballI 1);
by (induct_tac "j" 1);
by (fast_tac (claset() addSIs [Ramseyi0]) 1);
by (fast_tac (claset() addSDs [bspec]
 		       addSIs [add_type,Ramsey_step_lemma]) 1);
qed "ramsey_lemma";

(*Final statement in a tidy form, without succ(...) *)
Goal "[| i \\<in> nat;  j \\<in> nat |] ==> \\<exists>n \\<in> nat. Ramsey(n,i,j)";
by (best_tac (claset() addDs [ramsey_lemma]) 1);
qed "ramsey";

(*Compute Ramsey numbers according to proof above -- which, actually,
  does not constrain the base case values at all!*)
fun ram 0 j = 1
  | ram i 0 = 1
  | ram i j = ram (i-1) j + ram i (j-1);

(*Previous proof gave the following Ramsey numbers, which are smaller than
  those above by one!*)
fun ram' 0 j = 0
  | ram' i 0 = 0
  | ram' i j = ram' (i-1) j + ram' i (j-1) + 1;
