(*  Title: 	ZF/ex/ramsey.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
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

open Ramsey;

(*** Cliques and Independent sets ***)

goalw Ramsey.thy [Clique_def] "Clique(0,V,E)";
by (fast_tac ZF_cs 1);
val Clique0 = result();

goalw Ramsey.thy [Clique_def]
    "!!C V E. [| Clique(C,V',E);  V'<=V |] ==> Clique(C,V,E)";
by (fast_tac ZF_cs 1);
val Clique_superset = result();

goalw Ramsey.thy [Indept_def] "Indept(0,V,E)";
by (fast_tac ZF_cs 1);
val Indept0 = result();

val prems = goalw Ramsey.thy [Indept_def]
    "!!I V E. [| Indept(I,V',E);  V'<=V |] ==> Indept(I,V,E)";
by (fast_tac ZF_cs 1);
val Indept_superset = result();

(*** Atleast ***)

goalw Ramsey.thy [Atleast_def, inj_def, Pi_def, function_def] "Atleast(0,A)";
by (fast_tac ZF_cs 1);
val Atleast0 = result();

val [major] = goalw Ramsey.thy [Atleast_def]
    "Atleast(succ(m),A) ==> EX x:A. Atleast(m, A-{x})";
by (rtac (major RS exE) 1);
by (rtac bexI 1);
by (etac (inj_is_fun RS apply_type) 2);
by (rtac succI1 2);
by (rtac exI 1);
by (etac inj_succ_restrict 1);
val Atleast_succD = result();

val major::prems = goalw Ramsey.thy [Atleast_def]
    "[| Atleast(n,A);  A<=B |] ==> Atleast(n,B)";
by (rtac (major RS exE) 1);
by (rtac exI 1);
by (etac inj_weaken_type 1);
by (resolve_tac prems 1);
val Atleast_superset = result();

val prems = goalw Ramsey.thy [Atleast_def,succ_def]
    "[| Atleast(m,B);  b~: B |] ==> Atleast(succ(m), cons(b,B))";
by (cut_facts_tac prems 1);
by (etac exE 1);
by (rtac exI 1);
by (etac inj_extend 1);
by (rtac mem_not_refl 1);
by (assume_tac 1);
val Atleast_succI = result();

val prems = goal Ramsey.thy
    "[| Atleast(m, B-{x});  x: B |] ==> Atleast(succ(m), B)";
by (cut_facts_tac prems 1);
by (etac (Atleast_succI RS Atleast_superset) 1);
by (fast_tac ZF_cs 1);
by (fast_tac ZF_cs 1);
val Atleast_Diff_succI = result();

(*** Main Cardinality Lemma ***)

(*The #-succ(0) strengthens the original theorem statement, but precisely
  the same proof could be used!!*)
val prems = goal Ramsey.thy
    "m: nat ==> \
\    ALL n: nat. ALL A B. Atleast((m#+n) #- succ(0), A Un B) -->   \
\                         Atleast(m,A) | Atleast(n,B)";
by (nat_ind_tac "m" prems 1);
by (fast_tac (ZF_cs addSIs [Atleast0]) 1);
by (asm_simp_tac arith_ss 1);
by (rtac ballI 1);
by (rename_tac "n" 1);		(*simplifier does NOT preserve bound names!*)
by (nat_ind_tac "n" [] 1);
by (fast_tac (ZF_cs addSIs [Atleast0]) 1);
by (asm_simp_tac (arith_ss addsimps [add_succ_right]) 1);
by (safe_tac ZF_cs);
by (etac (Atleast_succD RS bexE) 1);
by (etac UnE 1);
(**case x:B.  Instantiate the 'ALL A B' induction hypothesis. **)
by (dres_inst_tac [("x1","A"), ("x","B-{x}")] (spec RS spec) 2);
by (etac (mp RS disjE) 2);
(*cases Atleast(succ(m1),A) and Atleast(succ(n1),B)*)
by (REPEAT (eresolve_tac [asm_rl, notE, Atleast_Diff_succI] 3));
(*proving the condition*)
by (etac Atleast_superset 2 THEN fast_tac ZF_cs 2);
(**case x:A.  Instantiate the 'ALL n:nat. ALL A B' induction hypothesis. **)
by (dres_inst_tac [("x2","succ(n1)"), ("x1","A-{x}"), ("x","B")] 
    (bspec RS spec RS spec) 1);
by (etac nat_succI 1);
by (etac (mp RS disjE) 1);
(*cases Atleast(succ(m1),A) and Atleast(succ(n1),B)*)
by (REPEAT (eresolve_tac [asm_rl, Atleast_Diff_succI, notE] 2));
(*proving the condition*)
by (asm_simp_tac (arith_ss addsimps [add_succ_right]) 1);
by (etac Atleast_superset 1 THEN fast_tac ZF_cs 1);
val pigeon2_lemma = result();

(* [| m:nat;  n:nat;  Atleast(m #+ n #- succ(0), A Un B) |] ==> 
   Atleast(m,A) | Atleast(n,B) *)
val pigeon2 = standard (pigeon2_lemma RS bspec RS spec RS spec RS mp);


(**** Ramsey's Theorem ****)

(** Base cases of induction; they now admit ANY Ramsey number **)

goalw Ramsey.thy [Ramsey_def] "Ramsey(n,0,j)";
by (fast_tac (ZF_cs addIs [Clique0,Atleast0]) 1);
val Ramsey0j = result();

goalw Ramsey.thy [Ramsey_def] "Ramsey(n,i,0)";
by (fast_tac (ZF_cs addIs [Indept0,Atleast0]) 1);
val Ramseyi0 = result();

(** Lemmas for induction step **)

(*The use of succ(m) here, rather than #-succ(0), simplifies the proof of 
  Ramsey_step_lemma.*)
val prems = goal Ramsey.thy
    "[| Atleast(m #+ n, A);  m: nat;  n: nat |] ==> \
\    Atleast(succ(m), {x:A. ~P(x)}) | Atleast(n, {x:A. P(x)})";
by (rtac (nat_succI RS pigeon2) 1);
by (simp_tac (arith_ss addsimps prems) 3);
by (rtac Atleast_superset 3);
by (REPEAT (resolve_tac prems 1));
by (fast_tac ZF_cs 1);
val Atleast_partition = result();

(*For the Atleast part, proves ~(a:I) from the second premise!*)
val prems = goalw Ramsey.thy [Symmetric_def,Indept_def]
    "[| Symmetric(E);  Indept(I, {z: V-{a}. <a,z> ~: E}, E);  a: V;  \
\       Atleast(j,I) |] ==>   \
\    Indept(cons(a,I), V, E) & Atleast(succ(j), cons(a,I))";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addSEs [Atleast_succI]) 1);	 (*34 secs*)
val Indept_succ = result();

val prems = goalw Ramsey.thy [Symmetric_def,Clique_def]
    "[| Symmetric(E);  Clique(C, {z: V-{a}. <a,z>:E}, E);  a: V;  \
\       Atleast(j,C) |] ==>   \
\    Clique(cons(a,C), V, E) & Atleast(succ(j), cons(a,C))";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addSEs [Atleast_succI]) 1);  (*41 secs*)
val Clique_succ = result();

(** Induction step **)

(*Published proofs gloss over the need for Ramsey numbers to be POSITIVE.*)
val ram1::ram2::prems = goalw Ramsey.thy [Ramsey_def] 
   "[| Ramsey(succ(m), succ(i), j);  Ramsey(n, i, succ(j));  \
\      m: nat;  n: nat |] ==> \
\   Ramsey(succ(m#+n), succ(i), succ(j))";
by (safe_tac ZF_cs);
by (etac (Atleast_succD RS bexE) 1);
by (eres_inst_tac [("P1","%z.<x,z>:E")] (Atleast_partition RS disjE) 1);
by (REPEAT (resolve_tac prems 1));
(*case m*)
by (rtac (ram1 RS spec RS spec RS mp RS disjE) 1);
by (fast_tac ZF_cs 1);
by (fast_tac (ZF_cs addEs [Clique_superset]) 1); (*easy -- given a Clique*)
by (safe_tac ZF_cs);
by (eresolve_tac (swapify [exI]) 1);		 (*ignore main EX quantifier*)
by (REPEAT (ares_tac [Indept_succ] 1));  	 (*make a bigger Indept*)
(*case n*)
by (rtac (ram2 RS spec RS spec RS mp RS disjE) 1);
by (fast_tac ZF_cs 1);
by (safe_tac ZF_cs);
by (rtac exI 1);
by (REPEAT (ares_tac [Clique_succ] 1));  	 (*make a bigger Clique*)
by (fast_tac (ZF_cs addEs [Indept_superset]) 1); (*easy -- given an Indept*)
val Ramsey_step_lemma = result();


(** The actual proof **)

(*Again, the induction requires Ramsey numbers to be positive.*)
val prems = goal Ramsey.thy
    "i: nat ==> ALL j: nat. EX n:nat. Ramsey(succ(n), i, j)";
by (nat_ind_tac "i" prems 1);
by (fast_tac (ZF_cs addSIs [nat_0I,Ramsey0j]) 1);
by (rtac ballI 1);
by (nat_ind_tac "j" [] 1);
by (fast_tac (ZF_cs addSIs [nat_0I,Ramseyi0]) 1);
by (dres_inst_tac [("x","succ(j1)")] bspec 1);
by (REPEAT (eresolve_tac [nat_succI,bexE] 1));
by (rtac bexI 1);
by (rtac Ramsey_step_lemma 1);
by (REPEAT (ares_tac [nat_succI,add_type] 1));
val ramsey_lemma = result();

(*Final statement in a tidy form, without succ(...) *)
val prems = goal Ramsey.thy
    "[| i: nat;  j: nat |] ==> EX n:nat. Ramsey(n,i,j)";
by (rtac (ramsey_lemma RS bspec RS bexE) 1);
by (etac bexI 3);
by (REPEAT (ares_tac (prems@[nat_succI]) 1));
val ramsey = result();

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
