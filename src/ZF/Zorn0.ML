(*  Title: 	ZF/Zorn0.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Preamble to proofs from the paper
    Abrial & Laffitte, 
    Towards the Mechanization of the Proofs of Some 
    Classical Theorems of Set Theory. 
*)


(*** Section 1.  Mathematical Preamble ***)

goal ZF.thy "!!A B C. (ALL x:C. x<=A | B<=x) ==> Union(C)<=A | B<=Union(C)";
by (fast_tac ZF_cs 1);
val Union_lemma0 = result();

goal ZF.thy
    "!!A B C. [| c:C; ALL x:C. A<=x | x<=B |] ==> A<=Inter(C) | Inter(C)<=B";
by (fast_tac ZF_cs 1);
val Inter_lemma0 = result();

open Zorn0;

(*** Section 2.  The Transfinite Construction ***)

goalw Zorn0.thy [increasing_def]
    "!!f A. f: increasing(A) ==> f: Pow(A)->Pow(A)";
by (eresolve_tac [CollectD1] 1);
val increasingD1 = result();

goalw Zorn0.thy [increasing_def]
    "!!f A. [| f: increasing(A); x<=A |] ==> x <= f`x";
by (eresolve_tac [CollectD2 RS spec RS mp] 1);
by (assume_tac 1);
val increasingD2 = result();

goal Zorn0.thy
    "!!next S. [| X : Pow(S);  next: increasing(S) |] ==> next`X : Pow(S)";
by (eresolve_tac [increasingD1 RS apply_type] 1);
by (assume_tac 1);
val next_bounded = result();

(*Trivial to prove here; hard to prove within Inductive_Fun*)
goal ZF.thy "!!Y. Y : Pow(Pow(A)) ==> Union(Y) : Pow(A)";
by (fast_tac ZF_cs 1);
val Union_in_Pow = result();

(** We could make the inductive definition conditional on next: increasing(S)
    but instead we make this a side-condition of an introduction rule.  Thus
    the induction rule lets us assume that condition!  Many inductive proofs
    are therefore unconditional.
**)
    

