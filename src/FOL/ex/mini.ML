(*  Title: 	FOL/ex/mini
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Classical First-Order Logic

Conversion to nnf/miniscope format: pushing quantifiers in

Demonstration of formula rewriting by proof
*)

val ccontr = FalseE RS classical;

(**** Negation Normal Form ****)

(*** de Morgan laws ***)

fun prove_fun s = 
 (writeln s;  
  prove_goal FOL.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
		  (Cla.fast_tac FOL_cs 1) ]));

val demorgans = map prove_fun
    		  ["~(P&Q) <-> ~P | ~Q",
		   "~(P|Q) <-> ~P & ~Q",
		   "~~P <-> P",
		   "~(ALL x.P(x)) <-> (EX x. ~P(x))",
		   "~(EX x.P(x)) <-> (ALL x. ~P(x))"];

(*** Removal of --> and <-> (positive and negative occurrences) ***)
(*Last one is important for computing a compact CNF*)
val nnf_rews = map prove_fun
		["(P-->Q) <-> (~P | Q)",
		 "~(P-->Q) <-> (P & ~Q)",
		 "(P<->Q) <-> (~P | Q) & (~Q | P)",
		 "~(P<->Q) <-> (P | Q) & (~P | ~Q)"];

(* BEWARE: rewrite rules for <-> can confuse the simplifier!! *)

(*** Pushing in the existential quantifiers ***)

val ex_rews = map prove_fun 
		["(EX x. P) <-> P",
		 "(EX x. P(x) & Q) <-> (EX x.P(x)) & Q",
		 "(EX x. P & Q(x)) <-> P & (EX x.Q(x))",
		 "(EX x. P(x) | Q(x)) <-> (EX x.P(x)) | (EX x.Q(x))",
		 "(EX x. P(x) | Q) <-> (EX x.P(x)) | Q",
		 "(EX x. P | Q(x)) <-> P | (EX x.Q(x))"];

(*** Pushing in the universal quantifiers ***)

val all_rews = map prove_fun
		["(ALL x. P) <-> P",
		 "(ALL x. P(x) & Q(x)) <-> (ALL x.P(x)) & (ALL x.Q(x))",
		 "(ALL x. P(x) & Q) <-> (ALL x.P(x)) & Q",
		 "(ALL x. P & Q(x)) <-> P & (ALL x.Q(x))",
		 "(ALL x. P(x) | Q) <-> (ALL x.P(x)) | Q",
		 "(ALL x. P | Q(x)) <-> P | (ALL x.Q(x))"];


val mini_ss = 
  empty_ss 
  setmksimps (map mk_meta_eq o atomize o gen_all)
  setsolver  (fn prems => resolve_tac (triv_rls@prems) 
	                  ORELSE' assume_tac
	                  ORELSE' etac FalseE)
  setsubgoaler asm_simp_tac
  addsimps (demorgans @ nnf_rews @ ex_rews @ all_rews);

val mini_tac = rtac ccontr THEN' asm_full_simp_tac mini_ss;

