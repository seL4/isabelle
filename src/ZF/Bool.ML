(*  Title: 	ZF/bool
    ID:         $Id$
    Author: 	Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For ZF/bool.thy.  Booleans in Zermelo-Fraenkel Set Theory 
*)

open Bool;

val bool_defs = [bool_def,one_def,cond_def];

(* Introduction rules *)

goalw Bool.thy bool_defs "1 : bool";
by (rtac (consI1 RS consI2) 1);
val bool_1I = result();

goalw Bool.thy bool_defs "0 : bool";
by (rtac consI1 1);
val bool_0I = result();

goalw Bool.thy bool_defs "~ 1=0";
by (rtac succ_not_0 1);
val one_not_0 = result();

(** 1=0 ==> R **)
val one_neq_0 = one_not_0 RS notE;

val prems = goalw Bool.thy bool_defs "[| c: bool;  P(1);  P(0) |] ==> P(c)";
by (cut_facts_tac prems 1);
by (fast_tac ZF_cs 1);
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
by (rtac (cond_0 RS ssubst) 2);
by (resolve_tac prems 2);
by (rtac (cond_1 RS ssubst) 1);
by (resolve_tac prems 1);
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

val bool_rews = [cond_1,cond_0,not_1,not_0,and_1,and_0,or_1,or_0,xor_1,xor_0];

