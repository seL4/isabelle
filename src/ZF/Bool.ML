(*  Title: 	ZF/bool
    ID:         $Id$
    Author: 	Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For ZF/bool.thy.  Booleans in Zermelo-Fraenkel Set Theory 
*)

open Bool;

val bool_defs = [bool_def,cond_def];

(* Introduction rules *)

goalw Bool.thy bool_defs "1 : bool";
by (rtac (consI1 RS consI2) 1);
val bool_1I = result();

goalw Bool.thy bool_defs "0 : bool";
by (rtac consI1 1);
val bool_0I = result();

goalw Bool.thy bool_defs "1~=0";
by (rtac succ_not_0 1);
val one_not_0 = result();

(** 1=0 ==> R **)
val one_neq_0 = one_not_0 RS notE;

val major::prems = goalw Bool.thy bool_defs
    "[| c: bool;  c=1 ==> P;  c=0 ==> P |] ==> P";
by (rtac (major RS consE) 1);
by (REPEAT (eresolve_tac (singletonE::prems) 1));
val boolE = result();

(** cond **)

(*1 means true*)
goalw Bool.thy bool_defs "cond(1,c,d) = c";
by (rtac (refl RS if_P) 1);
val cond_1 = result();

(*0 means false*)
goalw Bool.thy bool_defs "cond(0,c,d) = d";
by (rtac (succ_not_0 RS not_sym RS if_not_P) 1);
val cond_0 = result();

val major::prems = goal Bool.thy 
    "[|  b: bool;  c: A(1);  d: A(0) |] ==> cond(b,c,d): A(b)";
by (rtac (major RS boolE) 1);
by (asm_simp_tac (ZF_ss addsimps (cond_1::prems)) 1);
by (asm_simp_tac (ZF_ss addsimps (cond_0::prems)) 1);
val cond_type = result();

val [rew] = goal Bool.thy "[| !!b. j(b)==cond(b,c,d) |] ==> j(1) = c";
by (rewtac rew);
by (rtac cond_1 1);
val def_cond_1 = result();

val [rew] = goal Bool.thy "[| !!b. j(b)==cond(b,c,d) |] ==> j(0) = d";
by (rewtac rew);
by (rtac cond_0 1);
val def_cond_0 = result();

fun conds def = [standard (def RS def_cond_1), standard (def RS def_cond_0)];

val [not_1,not_0] = conds not_def;

val [and_1,and_0] = conds and_def;

val [or_1,or_0] = conds or_def;

val [xor_1,xor_0] = conds xor_def;

val not_type = prove_goalw Bool.thy [not_def]
    "a:bool ==> not(a) : bool"
 (fn prems=> [ (typechk_tac (prems@[bool_1I, bool_0I, cond_type])) ]);

val and_type = prove_goalw Bool.thy [and_def]
    "[| a:bool;  b:bool |] ==> a and b : bool"
 (fn prems=> [ (typechk_tac (prems@[bool_1I, bool_0I, cond_type])) ]);

val or_type = prove_goalw Bool.thy [or_def]
    "[| a:bool;  b:bool |] ==> a or b : bool"
 (fn prems=> [ (typechk_tac (prems@[bool_1I, bool_0I, cond_type])) ]);

val xor_type = prove_goalw Bool.thy [xor_def]
    "[| a:bool;  b:bool |] ==> a xor b : bool"
 (fn prems=> [ (typechk_tac(prems@[bool_1I, bool_0I, cond_type, not_type])) ]);

val bool_typechecks = [bool_1I, bool_0I, cond_type, not_type, and_type, 
		       or_type, xor_type]

val bool_simps = [cond_1,cond_0,not_1,not_0,and_1,and_0,or_1,or_0,xor_1,xor_0];

val bool_ss0 = ZF_ss addsimps bool_simps;

fun bool0_tac i =
    EVERY [etac boolE i, asm_simp_tac bool_ss0 (i+1), asm_simp_tac bool_ss0 i];

(*** Laws for 'not' ***)

goal Bool.thy "!!a. a:bool ==> not(not(a)) = a";
by (bool0_tac 1);
val not_not = result();

goal Bool.thy "!!a b. a:bool ==> not(a and b) = not(a) or not(b)";
by (bool0_tac 1);
val not_and = result();

goal Bool.thy "!!a b. a:bool ==> not(a or b) = not(a) and not(b)";
by (bool0_tac 1);
val not_or = result();

(*** Laws about 'and' ***)

goal Bool.thy "!!a. a: bool ==> a and a = a";
by (bool0_tac 1);
val and_absorb = result();

goal Bool.thy "!!a b. [| a: bool; b:bool |] ==> a and b = b and a";
by (etac boolE 1);
by (bool0_tac 1);
by (bool0_tac 1);
val and_commute = result();

goal Bool.thy
 "!!a. a: bool ==> (a and b) and c  =  a and (b and c)";
by (bool0_tac 1);
val and_assoc = result();

goal Bool.thy
 "!!a. [| a: bool; b:bool; c:bool |] ==> \
\      (a or b) and c  =  (a and c) or (b and c)";
by (REPEAT (bool0_tac 1));
val and_or_distrib = result();

(** binary orion **)

goal Bool.thy "!!a. a: bool ==> a or a = a";
by (bool0_tac 1);
val or_absorb = result();

goal Bool.thy "!!a b. [| a: bool; b:bool |] ==> a or b = b or a";
by (etac boolE 1);
by (bool0_tac 1);
by (bool0_tac 1);
val or_commute = result();

goal Bool.thy "!!a. a: bool ==> (a or b) or c  =  a or (b or c)";
by (bool0_tac 1);
val or_assoc = result();

goal Bool.thy
 "!!a b c. [| a: bool; b: bool; c: bool |] ==> \
\          (a and b) or c  =  (a or c) and (b or c)";
by (REPEAT (bool0_tac 1));
val or_and_distrib = result();

