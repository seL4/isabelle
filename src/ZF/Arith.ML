(*  Title:      ZF/arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For arith.thy.  Arithmetic operators and their definitions

Proofs about elementary arithmetic: addition, multiplication, etc.

Could prove def_rec_0, def_rec_succ...
*)

open Arith;

(*"Difference" is subtraction of natural numbers.
  There are no negative numbers; we have
     m #- n = 0  iff  m<=n   and     m #- n = succ(k) iff m>n.
  Also, rec(m, 0, %z w.z) is pred(m).   
*)

(** rec -- better than nat_rec; the succ case has no type requirement! **)

val rec_trans = rec_def RS def_transrec RS trans;

goal Arith.thy "rec(0,a,b) = a";
by (rtac rec_trans 1);
by (rtac nat_case_0 1);
qed "rec_0";

goal Arith.thy "rec(succ(m),a,b) = b(m, rec(m,a,b))";
by (rtac rec_trans 1);
by (simp_tac (ZF_ss addsimps [nat_case_succ, nat_succI]) 1);
qed "rec_succ";

val major::prems = goal Arith.thy
    "[| n: nat;  \
\       a: C(0);  \
\       !!m z. [| m: nat;  z: C(m) |] ==> b(m,z): C(succ(m))  \
\    |] ==> rec(n,a,b) : C(n)";
by (rtac (major RS nat_induct) 1);
by (ALLGOALS
    (asm_simp_tac (ZF_ss addsimps (prems@[rec_0,rec_succ]))));
qed "rec_type";

val nat_le_refl = nat_into_Ord RS le_refl;

val nat_typechecks = [rec_type, nat_0I, nat_1I, nat_succI, Ord_nat];

val nat_simps = [rec_0, rec_succ, not_lt0, nat_0_le, le0_iff, succ_le_iff,
                 nat_le_refl];

val nat_ss = ZF_ss addsimps (nat_simps @ nat_typechecks);


(** Addition **)

qed_goalw "add_type" Arith.thy [add_def]
    "[| m:nat;  n:nat |] ==> m #+ n : nat"
 (fn prems=> [ (typechk_tac (prems@nat_typechecks@ZF_typechecks)) ]);

qed_goalw "add_0" Arith.thy [add_def]
    "0 #+ n = n"
 (fn _ => [ (rtac rec_0 1) ]);

qed_goalw "add_succ" Arith.thy [add_def]
    "succ(m) #+ n = succ(m #+ n)"
 (fn _=> [ (rtac rec_succ 1) ]); 

(** Multiplication **)

qed_goalw "mult_type" Arith.thy [mult_def]
    "[| m:nat;  n:nat |] ==> m #* n : nat"
 (fn prems=>
  [ (typechk_tac (prems@[add_type]@nat_typechecks@ZF_typechecks)) ]);

qed_goalw "mult_0" Arith.thy [mult_def]
    "0 #* n = 0"
 (fn _ => [ (rtac rec_0 1) ]);

qed_goalw "mult_succ" Arith.thy [mult_def]
    "succ(m) #* n = n #+ (m #* n)"
 (fn _ => [ (rtac rec_succ 1) ]); 

(** Difference **)

qed_goalw "diff_type" Arith.thy [diff_def]
    "[| m:nat;  n:nat |] ==> m #- n : nat"
 (fn prems=> [ (typechk_tac (prems@nat_typechecks@ZF_typechecks)) ]);

qed_goalw "diff_0" Arith.thy [diff_def]
    "m #- 0 = m"
 (fn _ => [ (rtac rec_0 1) ]);

qed_goalw "diff_0_eq_0" Arith.thy [diff_def]
    "n:nat ==> 0 #- n = 0"
 (fn [prem]=>
  [ (rtac (prem RS nat_induct) 1),
    (ALLGOALS (asm_simp_tac nat_ss)) ]);

(*Must simplify BEFORE the induction!!  (Else we get a critical pair)
  succ(m) #- succ(n)   rewrites to   pred(succ(m) #- n)  *)
qed_goalw "diff_succ_succ" Arith.thy [diff_def]
    "[| m:nat;  n:nat |] ==> succ(m) #- succ(n) = m #- n"
 (fn prems=>
  [ (asm_simp_tac (nat_ss addsimps prems) 1),
    (nat_ind_tac "n" prems 1),
    (ALLGOALS (asm_simp_tac (nat_ss addsimps prems))) ]);

val prems = goal Arith.thy 
    "[| m:nat;  n:nat |] ==> m #- n le m";
by (rtac (prems MRS diff_induct) 1);
by (etac leE 3);
by (ALLGOALS
    (asm_simp_tac
     (nat_ss addsimps (prems @ [le_iff, diff_0, diff_0_eq_0, 
                                diff_succ_succ, nat_into_Ord]))));
qed "diff_le_self";

(*** Simplification over add, mult, diff ***)

val arith_typechecks = [add_type, mult_type, diff_type];
val arith_simps = [add_0, add_succ,
                   mult_0, mult_succ,
                   diff_0, diff_0_eq_0, diff_succ_succ];

val arith_ss = nat_ss addsimps (arith_simps@arith_typechecks);

(*** Addition ***)

(*Associative law for addition*)
qed_goal "add_assoc" Arith.thy 
    "m:nat ==> (m #+ n) #+ k = m #+ (n #+ k)"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]);

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
qed_goal "add_0_right" Arith.thy
    "m:nat ==> m #+ 0 = m"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]); 

qed_goal "add_succ_right" Arith.thy
    "m:nat ==> m #+ succ(n) = succ(m #+ n)"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]); 

(*Commutative law for addition*)  
qed_goal "add_commute" Arith.thy 
    "!!m n. [| m:nat;  n:nat |] ==> m #+ n = n #+ m"
 (fn _ =>
  [ (nat_ind_tac "n" [] 1),
    (ALLGOALS
     (asm_simp_tac (arith_ss addsimps [add_0_right, add_succ_right]))) ]);

(*for a/c rewriting*)
qed_goal "add_left_commute" Arith.thy
    "!!m n k. [| m:nat;  n:nat |] ==> m#+(n#+k)=n#+(m#+k)"
 (fn _ => [asm_simp_tac (ZF_ss addsimps [add_assoc RS sym, add_commute]) 1]);

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

(*Cancellation law on the left*)
val [eqn,knat] = goal Arith.thy 
    "[| k #+ m = k #+ n;  k:nat |] ==> m=n";
by (rtac (eqn RS rev_mp) 1);
by (nat_ind_tac "k" [knat] 1);
by (ALLGOALS (simp_tac arith_ss));
by (fast_tac ZF_cs 1);
qed "add_left_cancel";

(*** Multiplication ***)

(*right annihilation in product*)
qed_goal "mult_0_right" Arith.thy 
    "!!m. m:nat ==> m #* 0 = 0"
 (fn _=>
  [ (nat_ind_tac "m" [] 1),
    (ALLGOALS (asm_simp_tac arith_ss))  ]);

(*right successor law for multiplication*)
qed_goal "mult_succ_right" Arith.thy 
    "!!m n. [| m:nat;  n:nat |] ==> m #* succ(n) = m #+ (m #* n)"
 (fn _ =>
  [ (nat_ind_tac "m" [] 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps add_ac))) ]);

(*Commutative law for multiplication*)
qed_goal "mult_commute" Arith.thy 
    "[| m:nat;  n:nat |] ==> m #* n = n #* m"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac
             (arith_ss addsimps (prems@[mult_0_right, mult_succ_right])))) ]);

(*addition distributes over multiplication*)
qed_goal "add_mult_distrib" Arith.thy 
    "!!m n. [| m:nat;  k:nat |] ==> (m #+ n) #* k = (m #* k) #+ (n #* k)"
 (fn _=>
  [ (etac nat_induct 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps [add_assoc RS sym]))) ]);

(*Distributive law on the left; requires an extra typing premise*)
qed_goal "add_mult_distrib_left" Arith.thy 
    "!!m. [| m:nat;  n:nat;  k:nat |] ==> k #* (m #+ n) = (k #* m) #+ (k #* n)"
 (fn prems=>
  [ (nat_ind_tac "m" [] 1),
    (asm_simp_tac (arith_ss addsimps [mult_0_right]) 1),
    (asm_simp_tac (arith_ss addsimps ([mult_succ_right] @ add_ac)) 1) ]);

(*Associative law for multiplication*)
qed_goal "mult_assoc" Arith.thy 
    "!!m n k. [| m:nat;  n:nat;  k:nat |] ==> (m #* n) #* k = m #* (n #* k)"
 (fn _=>
  [ (etac nat_induct 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps [add_mult_distrib]))) ]);

(*for a/c rewriting*)
qed_goal "mult_left_commute" Arith.thy 
    "!!m n k. [| m:nat;  n:nat;  k:nat |] ==> m #* (n #* k) = n #* (m #* k)"
 (fn _ => [rtac (mult_commute RS trans) 1, 
           rtac (mult_assoc RS trans) 3, 
           rtac (mult_commute RS subst_context) 6,
           REPEAT (ares_tac [mult_type] 1)]);

val mult_ac = [mult_assoc,mult_commute,mult_left_commute];


(*** Difference ***)

qed_goal "diff_self_eq_0" Arith.thy 
    "m:nat ==> m #- m = 0"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]);

(*Addition is the inverse of subtraction*)
goal Arith.thy "!!m n. [| n le m;  m:nat |] ==> n #+ (m#-n) = m";
by (forward_tac [lt_nat_in_nat] 1);
by (etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac arith_ss));
qed "add_diff_inverse";

(*Subtraction is the inverse of addition. *)
val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> (n#+m) #- n = m";
by (rtac (nnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [mnat])));
qed "diff_add_inverse";

goal Arith.thy
    "!!m n. [| m:nat;  n:nat |] ==> (m#+n) #- n = m";
by (res_inst_tac [("m1","m")] (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [diff_add_inverse] 1));
qed "diff_add_inverse2";

val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> n #- (n#+m) = 0";
by (rtac (nnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [mnat])));
qed "diff_add_0";


(*** Remainder ***)

goal Arith.thy "!!m n. [| 0<n;  n le m;  m:nat |] ==> m #- n < m";
by (forward_tac [lt_nat_in_nat] 1 THEN etac nat_succI 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (nat_ss addsimps [diff_le_self,diff_succ_succ])));
qed "div_termination";

val div_rls =   (*for mod and div*)
    nat_typechecks @
    [Ord_transrec_type, apply_type, div_termination RS ltD, if_type,
     nat_into_Ord, not_lt_iff_le RS iffD1];

val div_ss = ZF_ss addsimps [nat_into_Ord, div_termination RS ltD,
                             not_lt_iff_le RS iffD2];

(*Type checking depends upon termination!*)
goalw Arith.thy [mod_def] "!!m n. [| 0<n;  m:nat;  n:nat |] ==> m mod n : nat";
by (REPEAT (ares_tac div_rls 1 ORELSE etac lt_trans 1));
qed "mod_type";

goal Arith.thy "!!m n. [| 0<n;  m<n |] ==> m mod n = m";
by (rtac (mod_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "mod_less";

goal Arith.thy "!!m n. [| 0<n;  n le m;  m:nat |] ==> m mod n = (m#-n) mod n";
by (forward_tac [lt_nat_in_nat] 1 THEN etac nat_succI 1);
by (rtac (mod_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "mod_geq";

(*** Quotient ***)

(*Type checking depends upon termination!*)
goalw Arith.thy [div_def]
    "!!m n. [| 0<n;  m:nat;  n:nat |] ==> m div n : nat";
by (REPEAT (ares_tac div_rls 1 ORELSE etac lt_trans 1));
qed "div_type";

goal Arith.thy "!!m n. [| 0<n;  m<n |] ==> m div n = 0";
by (rtac (div_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "div_less";

goal Arith.thy
 "!!m n. [| 0<n;  n le m;  m:nat |] ==> m div n = succ((m#-n) div n)";
by (forward_tac [lt_nat_in_nat] 1 THEN etac nat_succI 1);
by (rtac (div_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "div_geq";

(*Main Result.*)
goal Arith.thy
    "!!m n. [| 0<n;  m:nat;  n:nat |] ==> (m div n)#*n #+ m mod n = m";
by (etac complete_induct 1);
by (excluded_middle_tac "x<n" 1);
(*case x<n*)
by (asm_simp_tac (arith_ss addsimps [mod_less, div_less]) 2);
(*case n le x*)
by (asm_full_simp_tac
     (arith_ss addsimps [not_lt_iff_le, nat_into_Ord,
                         mod_geq, div_geq, add_assoc,
                         div_termination RS ltD, add_diff_inverse]) 1);
qed "mod_div_equality";


(**** Additional theorems about "le" ****)

goal Arith.thy "!!m n. [| m:nat;  n:nat |] ==> m le m #+ n";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac arith_ss));
qed "add_le_self";

goal Arith.thy "!!m n. [| m:nat;  n:nat |] ==> m le n #+ m";
by (rtac (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [add_le_self] 1));
qed "add_le_self2";

(** Monotonicity of addition **)

(*strict, in 1st argument*)
goal Arith.thy "!!i j k. [| i<j; j:nat; k:nat |] ==> i#+k < j#+k";
by (forward_tac [lt_nat_in_nat] 1);
by (assume_tac 1);
by (etac succ_lt_induct 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [leI])));
qed "add_lt_mono1";

(*strict, in both arguments*)
goal Arith.thy "!!i j k l. [| i<j; k<l; j:nat; l:nat |] ==> i#+k < j#+l";
by (rtac (add_lt_mono1 RS lt_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat] 1));
by (EVERY [rtac (add_commute RS ssubst) 1,
           rtac (add_commute RS ssubst) 3,
           rtac add_lt_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat] 1));
qed "add_lt_mono";

(*A [clumsy] way of lifting < monotonicity to le monotonicity *)
val lt_mono::ford::prems = goal Ordinal.thy
     "[| !!i j. [| i<j; j:k |] ==> f(i) < f(j); \
\        !!i. i:k ==> Ord(f(i));                \
\        i le j;  j:k                           \
\     |] ==> f(i) le f(j)";
by (cut_facts_tac prems 1);
by (fast_tac (lt_cs addSIs [lt_mono,ford] addSEs [leE]) 1);
qed "Ord_lt_mono_imp_le_mono";

(*le monotonicity, 1st argument*)
goal Arith.thy
    "!!i j k. [| i le j; j:nat; k:nat |] ==> i#+k le j#+k";
by (res_inst_tac [("f", "%j.j#+k")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [add_lt_mono1, add_type RS nat_into_Ord] 1));
qed "add_le_mono1";

(* le monotonicity, BOTH arguments*)
goal Arith.thy
    "!!i j k. [| i le j; k le l; j:nat; l:nat |] ==> i#+k le j#+l";
by (rtac (add_le_mono1 RS le_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
by (EVERY [rtac (add_commute RS ssubst) 1,
           rtac (add_commute RS ssubst) 3,
           rtac add_le_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
qed "add_le_mono";
