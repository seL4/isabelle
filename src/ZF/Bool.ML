(*  Title:      ZF/bool
    ID:         $Id$
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Booleans in Zermelo-Fraenkel Set Theory 
*)

val bool_defs = [bool_def,cond_def];

Goalw [succ_def] "{0} = 1";
by (rtac refl 1);
qed "singleton_0";

(* Introduction rules *)

Goalw bool_defs "1 : bool";
by (rtac (consI1 RS consI2) 1);
qed "bool_1I";

Goalw bool_defs "0 : bool";
by (rtac consI1 1);
qed "bool_0I";

Addsimps [bool_1I, bool_0I];
AddTCs   [bool_1I, bool_0I];

Goalw bool_defs "1~=0";
by (rtac succ_not_0 1);
qed "one_not_0";

(** 1=0 ==> R **)
val one_neq_0 = one_not_0 RS notE;

val major::prems = Goalw bool_defs
    "[| c: bool;  c=1 ==> P;  c=0 ==> P |] ==> P";
by (rtac (major RS consE) 1);
by (REPEAT (eresolve_tac (singletonE::prems) 1));
qed "boolE";

(** cond **)

(*1 means true*)
Goalw bool_defs "cond(1,c,d) = c";
by (rtac (refl RS if_P) 1);
qed "cond_1";

(*0 means false*)
Goalw bool_defs "cond(0,c,d) = d";
by (rtac (succ_not_0 RS not_sym RS if_not_P) 1);
qed "cond_0";

Addsimps [cond_1, cond_0];

fun bool_tac i = fast_tac (claset() addSEs [boolE] addss (simpset())) i;


Goal "[| b: bool;  c: A(1);  d: A(0) |] ==> cond(b,c,d): A(b)";
by (bool_tac 1);
qed "cond_type";
AddTCs [cond_type];

(*For Simp_tac and Blast_tac*)
Goal "[| b: bool;  c: A;  d: A |] ==> cond(b,c,d): A";
by (bool_tac 1);
qed "cond_simple_type";

val [rew] = Goal "[| !!b. j(b)==cond(b,c,d) |] ==> j(1) = c";
by (rewtac rew);
by (rtac cond_1 1);
qed "def_cond_1";

val [rew] = Goal "[| !!b. j(b)==cond(b,c,d) |] ==> j(0) = d";
by (rewtac rew);
by (rtac cond_0 1);
qed "def_cond_0";

fun conds def = [standard (def RS def_cond_1), standard (def RS def_cond_0)];

val [not_1,not_0] = conds not_def;
val [and_1,and_0] = conds and_def;
val [or_1,or_0]   = conds or_def;
val [xor_1,xor_0] = conds xor_def;

Addsimps [not_1,not_0,and_1,and_0,or_1,or_0,xor_1,xor_0];

Goalw [not_def] "a:bool ==> not(a) : bool";
by (Asm_simp_tac 1);
qed "not_type";

Goalw [and_def] "[| a:bool;  b:bool |] ==> a and b : bool";
by (Asm_simp_tac 1);
qed "and_type";

Goalw [or_def] "[| a:bool;  b:bool |] ==> a or b : bool";
by (Asm_simp_tac 1);
qed "or_type";

AddTCs [not_type, and_type, or_type];

Goalw [xor_def] "[| a:bool;  b:bool |] ==> a xor b : bool";
by (Asm_simp_tac 1);
qed "xor_type";

AddTCs [xor_type];

val bool_typechecks = [bool_1I, bool_0I, cond_type, not_type, and_type, 
                       or_type, xor_type];

(*** Laws for 'not' ***)

Goal "a:bool ==> not(not(a)) = a";
by (bool_tac 1);
qed "not_not";

Goal "a:bool ==> not(a and b) = not(a) or not(b)";
by (bool_tac 1);
qed "not_and";

Goal "a:bool ==> not(a or b) = not(a) and not(b)";
by (bool_tac 1);
qed "not_or";

Addsimps [not_not, not_and, not_or];

(*** Laws about 'and' ***)

Goal "a: bool ==> a and a = a";
by (bool_tac 1);
qed "and_absorb";

Addsimps [and_absorb];

Goal "[| a: bool; b:bool |] ==> a and b = b and a";
by (bool_tac 1);
qed "and_commute";

Goal "a: bool ==> (a and b) and c  =  a and (b and c)";
by (bool_tac 1);
qed "and_assoc";

Goal "[| a: bool; b:bool; c:bool |] ==> \
\      (a or b) and c  =  (a and c) or (b and c)";
by (bool_tac 1);
qed "and_or_distrib";

(** binary orion **)

Goal "a: bool ==> a or a = a";
by (bool_tac 1);
qed "or_absorb";

Addsimps [or_absorb];

Goal "[| a: bool; b:bool |] ==> a or b = b or a";
by (bool_tac 1);
qed "or_commute";

Goal "a: bool ==> (a or b) or c  =  a or (b or c)";
by (bool_tac 1);
qed "or_assoc";

Goal "[| a: bool; b: bool; c: bool |] ==> \
\          (a and b) or c  =  (a or c) and (b or c)";
by (bool_tac 1);
qed "or_and_distrib";

