(*  Title: 	CCL/ex/nat
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For nat.thy.
*)

open Nat;

val nat_defs = [not_def,add_def,mult_def,sub_def,le_def,lt_def,ack_def,napply_def];

val natBs = map (fn s=>prove_goalw Nat.thy nat_defs s (fn _ => [simp_tac term_ss 1]))
     ["not(true) = false",
      "not(false) = true",
      "zero #+ n = n",
      "succ(n) #+ m = succ(n #+ m)",
      "zero #* n = zero",
      "succ(n) #* m = m #+ (n #* m)",
      "f^zero`a = a",
      "f^succ(n)`a = f(f^n`a)"];

val nat_ss = term_ss addsimps natBs;

(*** Lemma for napply ***)

val [prem] = goal Nat.thy "n:Nat ==> f^n`f(a) = f^succ(n)`a";
br (prem RS Nat_ind) 1;
by (ALLGOALS (asm_simp_tac nat_ss));
qed "napply_f";

(****)

val prems = goalw Nat.thy [add_def] "[| a:Nat;  b:Nat |] ==> a #+ b : Nat";
by (typechk_tac prems 1);
qed "addT";

val prems = goalw Nat.thy [mult_def] "[| a:Nat;  b:Nat |] ==> a #* b : Nat";
by (typechk_tac (addT::prems) 1);
qed "multT";

(* Defined to return zero if a<b *)
val prems = goalw Nat.thy [sub_def] "[| a:Nat;  b:Nat |] ==> a #- b : Nat";
by (typechk_tac (prems) 1);
by clean_ccs_tac;
be (NatPRI RS wfstI RS (NatPR_wf RS wmap_wf RS wfI)) 1;
qed "subT";

val prems = goalw Nat.thy [le_def] "[| a:Nat;  b:Nat |] ==> a #<= b : Bool";
by (typechk_tac (prems) 1);
by clean_ccs_tac;
be (NatPRI RS wfstI RS (NatPR_wf RS wmap_wf RS wfI)) 1;
qed "leT";

val prems = goalw Nat.thy [not_def,lt_def] "[| a:Nat;  b:Nat |] ==> a #< b : Bool";
by (typechk_tac (prems@[leT]) 1);
qed "ltT";

(* Correctness conditions for subtractive division **)

val prems = goalw Nat.thy [div_def] 
    "[| a:Nat;  b:{x:Nat.~x=zero} |] ==> a ## b : {x:Nat. DIV(a,b,x)}";
by (gen_ccs_tac (prems@[ltT,subT]) 1);

(* Termination Conditions for Ackermann's Function *)

val prems = goalw Nat.thy [ack_def]
    "[| a:Nat;  b:Nat |] ==> ackermann(a,b) : Nat";
by (gen_ccs_tac prems 1);
val relI = NatPR_wf RS (NatPR_wf RS lex_wf RS wfI);
by (REPEAT (eresolve_tac [NatPRI RS (lexI1 RS relI),NatPRI RS (lexI2 RS relI)] 1));
result();
