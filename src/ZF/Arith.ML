(*  Title:      ZF/Arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Arithmetic operators and their definitions

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
by (Simp_tac 1);
qed "rec_succ";

Addsimps [rec_0, rec_succ];

val major::prems = goal Arith.thy
    "[| n: nat;  \
\       a: C(0);  \
\       !!m z. [| m: nat;  z: C(m) |] ==> b(m,z): C(succ(m))  \
\    |] ==> rec(n,a,b) : C(n)";
by (rtac (major RS nat_induct) 1);
by (ALLGOALS
    (asm_simp_tac (!simpset addsimps prems)));
qed "rec_type";

Addsimps [rec_type, nat_0_le, nat_le_refl];
val nat_typechecks = [rec_type, nat_0I, nat_1I, nat_succI, Ord_nat];

goal Arith.thy "!!k. [| 0<k; k: nat |] ==> EX j: nat. k = succ(j)";
by (etac rev_mp 1);
by (etac nat_induct 1);
by (Simp_tac 1);
by (Blast_tac 1);
val lemma = result();

(* [| 0 < k; k: nat; !!j. [| j: nat; k = succ(j) |] ==> Q |] ==> Q *)
bind_thm ("zero_lt_natE", lemma RS bexE);


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

Addsimps [add_0, add_succ];

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

Addsimps [mult_0, mult_succ];

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
    (ALLGOALS (Asm_simp_tac)) ]);

(*Must simplify BEFORE the induction!!  (Else we get a critical pair)
  succ(m) #- succ(n)   rewrites to   pred(succ(m) #- n)  *)
qed_goalw "diff_succ_succ" Arith.thy [diff_def]
    "[| m:nat;  n:nat |] ==> succ(m) #- succ(n) = m #- n"
 (fn prems=>
  [ (asm_simp_tac (!simpset addsimps prems) 1),
    (nat_ind_tac "n" prems 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps prems))) ]);

Addsimps [diff_0, diff_0_eq_0, diff_succ_succ];

val prems = goal Arith.thy 
    "[| m:nat;  n:nat |] ==> m #- n le m";
by (rtac (prems MRS diff_induct) 1);
by (etac leE 3);
by (ALLGOALS
    (asm_simp_tac (!simpset addsimps (prems @ [le_iff, nat_into_Ord]))));
qed "diff_le_self";

(*** Simplification over add, mult, diff ***)

val arith_typechecks = [add_type, mult_type, diff_type];
Addsimps arith_typechecks;


(*** Addition ***)

(*Associative law for addition*)
qed_goal "add_assoc" Arith.thy 
    "m:nat ==> (m #+ n) #+ k = m #+ (n #+ k)"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps prems))) ]);

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
qed_goal "add_0_right" Arith.thy
    "m:nat ==> m #+ 0 = m"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps prems))) ]); 

qed_goal "add_succ_right" Arith.thy
    "m:nat ==> m #+ succ(n) = succ(m #+ n)"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps prems))) ]); 

Addsimps [add_0_right, add_succ_right];

(*Commutative law for addition*)  
qed_goal "add_commute" Arith.thy 
    "!!m n. [| m:nat;  n:nat |] ==> m #+ n = n #+ m"
 (fn _ =>
  [ (nat_ind_tac "n" [] 1),
    (ALLGOALS Asm_simp_tac) ]);

(*for a/c rewriting*)
qed_goal "add_left_commute" Arith.thy
    "!!m n k. [| m:nat;  n:nat |] ==> m#+(n#+k)=n#+(m#+k)"
 (fn _ => [asm_simp_tac(!simpset addsimps [add_assoc RS sym, add_commute]) 1]);

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

(*Cancellation law on the left*)
val [eqn,knat] = goal Arith.thy 
    "[| k #+ m = k #+ n;  k:nat |] ==> m=n";
by (rtac (eqn RS rev_mp) 1);
by (nat_ind_tac "k" [knat] 1);
by (ALLGOALS (Simp_tac));
qed "add_left_cancel";

(*** Multiplication ***)

(*right annihilation in product*)
qed_goal "mult_0_right" Arith.thy 
    "!!m. m:nat ==> m #* 0 = 0"
 (fn _=>
  [ (nat_ind_tac "m" [] 1),
    (ALLGOALS (Asm_simp_tac))  ]);

(*right successor law for multiplication*)
qed_goal "mult_succ_right" Arith.thy 
    "!!m n. [| m:nat;  n:nat |] ==> m #* succ(n) = m #+ (m #* n)"
 (fn _ =>
  [ (nat_ind_tac "m" [] 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps add_ac))) ]);

Addsimps [mult_0_right, mult_succ_right];

goal Arith.thy "!!n. n:nat ==> 1 #* n = n";
by (Asm_simp_tac 1);
qed "mult_1";

goal Arith.thy "!!n. n:nat ==> n #* 1 = n";
by (Asm_simp_tac 1);
qed "mult_1_right";

(*Commutative law for multiplication*)
qed_goal "mult_commute" Arith.thy 
    "!!m n. [| m:nat;  n:nat |] ==> m #* n = n #* m"
 (fn _=>
  [ (nat_ind_tac "m" [] 1),
    (ALLGOALS Asm_simp_tac) ]);

(*addition distributes over multiplication*)
qed_goal "add_mult_distrib" Arith.thy 
    "!!m n. [| m:nat;  k:nat |] ==> (m #+ n) #* k = (m #* k) #+ (n #* k)"
 (fn _=>
  [ (etac nat_induct 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps [add_assoc RS sym]))) ]);

(*Distributive law on the left; requires an extra typing premise*)
qed_goal "add_mult_distrib_left" Arith.thy 
    "!!m. [| m:nat;  n:nat;  k:nat |] ==> k #* (m #+ n) = (k #* m) #+ (k #* n)"
 (fn prems=>
  [ (nat_ind_tac "m" [] 1),
    (Asm_simp_tac 1),
    (asm_simp_tac (!simpset addsimps add_ac) 1) ]);

(*Associative law for multiplication*)
qed_goal "mult_assoc" Arith.thy 
    "!!m n k. [| m:nat;  n:nat;  k:nat |] ==> (m #* n) #* k = m #* (n #* k)"
 (fn _=>
  [ (etac nat_induct 1),
    (ALLGOALS (asm_simp_tac (!simpset addsimps [add_mult_distrib]))) ]);

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
    (ALLGOALS (asm_simp_tac (!simpset addsimps prems))) ]);

(*Addition is the inverse of subtraction*)
goal Arith.thy "!!m n. [| n le m;  m:nat |] ==> n #+ (m#-n) = m";
by (forward_tac [lt_nat_in_nat] 1);
by (etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "add_diff_inverse";

(*Proof is IDENTICAL to that above*)
goal Arith.thy "!!m n. [| n le m;  m:nat |] ==> succ(m) #- n = succ(m#-n)";
by (forward_tac [lt_nat_in_nat] 1);
by (etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_succ";

(** Subtraction is the inverse of addition. **)

val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> (n#+m) #- n = m";
by (rtac (nnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mnat])));
qed "diff_add_inverse";

goal Arith.thy
    "!!m n. [| m:nat;  n:nat |] ==> (m#+n) #- n = m";
by (res_inst_tac [("m1","m")] (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [diff_add_inverse] 1));
qed "diff_add_inverse2";

goal Arith.thy
    "!!k. [| k:nat; m: nat; n: nat |] ==> (k#+m) #- (k#+n) = m #- n";
by (nat_ind_tac "k" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_cancel";

goal Arith.thy
    "!!n. [| k:nat; m: nat; n: nat |] ==> (m#+k) #- (n#+k) = m #- n";
val add_commute_k = read_instantiate [("n","k")] add_commute;
by (asm_simp_tac (!simpset addsimps [add_commute_k, diff_cancel]) 1);
qed "diff_cancel2";

val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> n #- (n#+m) = 0";
by (rtac (nnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mnat])));
qed "diff_add_0";

(** Difference distributes over multiplication **)

goal Arith.thy 
  "!!m n. [| m:nat; n: nat; k:nat |] ==> (m #- n) #* k = (m #* k) #- (n #* k)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [diff_cancel])));
qed "diff_mult_distrib" ;

goal Arith.thy 
  "!!m. [| m:nat; n: nat; k:nat |] ==> k #* (m #- n) = (k #* m) #- (k #* n)";
val mult_commute_k = read_instantiate [("m","k")] mult_commute;
by (asm_simp_tac (!simpset addsimps 
                  [mult_commute_k, diff_mult_distrib]) 1);
qed "diff_mult_distrib2" ;

(*** Remainder ***)

goal Arith.thy "!!m n. [| 0<n;  n le m;  m:nat |] ==> m #- n < m";
by (forward_tac [lt_nat_in_nat] 1 THEN etac nat_succI 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [diff_le_self,diff_succ_succ])));
qed "div_termination";

val div_rls =   (*for mod and div*)
    nat_typechecks @
    [Ord_transrec_type, apply_type, div_termination RS ltD, if_type,
     nat_into_Ord, not_lt_iff_le RS iffD1];

val div_ss = (!simpset) addsimps [nat_into_Ord, div_termination RS ltD,
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

Addsimps [mod_type, mod_less, mod_geq];

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

Addsimps [div_type, div_less, div_geq];

(*A key result*)
goal Arith.thy
    "!!m n. [| 0<n;  m:nat;  n:nat |] ==> (m div n)#*n #+ m mod n = m";
by (etac complete_induct 1);
by (excluded_middle_tac "x<n" 1);
(*case x<n*)
by (Asm_simp_tac 2);
(*case n le x*)
by (asm_full_simp_tac
     (!simpset addsimps [not_lt_iff_le, nat_into_Ord, add_assoc,
                         div_termination RS ltD, add_diff_inverse]) 1);
qed "mod_div_equality";

(*** Further facts about mod (mainly for mutilated checkerboard ***)

goal Arith.thy
    "!!m n. [| 0<n;  m:nat;  n:nat |] ==> \
\           succ(m) mod n = if(succ(m mod n) = n, 0, succ(m mod n))";
by (etac complete_induct 1);
by (excluded_middle_tac "succ(x)<n" 1);
(* case succ(x) < n *)
by (asm_simp_tac (!simpset addsimps [mod_less, nat_le_refl RS lt_trans,
                                     succ_neq_self]) 2);
by (asm_simp_tac (!simpset addsimps [ltD RS mem_imp_not_eq]) 2);
(* case n le succ(x) *)
by (asm_full_simp_tac
     (!simpset addsimps [not_lt_iff_le, nat_into_Ord, mod_geq]) 1);
by (etac leE 1);
by (asm_simp_tac (!simpset addsimps [div_termination RS ltD, diff_succ, 
                                     mod_geq]) 1);
by (asm_simp_tac (!simpset addsimps [mod_less, diff_self_eq_0]) 1);
qed "mod_succ";

goal Arith.thy "!!m n. [| 0<n;  m:nat;  n:nat |] ==> m mod n < n";
by (etac complete_induct 1);
by (excluded_middle_tac "x<n" 1);
(*case x<n*)
by (asm_simp_tac (!simpset addsimps [mod_less]) 2);
(*case n le x*)
by (asm_full_simp_tac
     (!simpset addsimps [not_lt_iff_le, nat_into_Ord,
                         mod_geq, div_termination RS ltD]) 1);
qed "mod_less_divisor";


goal Arith.thy
    "!!k b. [| k: nat; b<2 |] ==> k mod 2 = b | k mod 2 = if(b=1,0,1)";
by (subgoal_tac "k mod 2: 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor RS ltD]) 2);
by (dtac ltD 1);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Blast_tac 1);
qed "mod2_cases";

goal Arith.thy "!!m. m:nat ==> succ(succ(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2: 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor RS ltD]) 2);
by (asm_simp_tac (!simpset addsimps [mod_succ] setloop step_tac (!claset)) 1);
qed "mod2_succ_succ";

goal Arith.thy "!!m. m:nat ==> (m#+m) mod 2 = 0";
by (etac nat_induct 1);
by (simp_tac (!simpset addsimps [mod_less]) 1);
by (asm_simp_tac (!simpset addsimps [mod2_succ_succ, add_succ_right]) 1);
qed "mod2_add_self";


(**** Additional theorems about "le" ****)

goal Arith.thy "!!m n. [| m:nat;  n:nat |] ==> m le m #+ n";
by (etac nat_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "add_le_self";

goal Arith.thy "!!m n. [| m:nat;  n:nat |] ==> m le n #+ m";
by (stac add_commute 1);
by (REPEAT (ares_tac [add_le_self] 1));
qed "add_le_self2";

(*** Monotonicity of Addition ***)

(*strict, in 1st argument; proof is by rule induction on 'less than'*)
goal Arith.thy "!!i j k. [| i<j; j:nat; k:nat |] ==> i#+k < j#+k";
by (forward_tac [lt_nat_in_nat] 1);
by (assume_tac 1);
by (etac succ_lt_induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [leI])));
qed "add_lt_mono1";

(*strict, in both arguments*)
goal Arith.thy "!!i j k l. [| i<j; k<l; j:nat; l:nat |] ==> i#+k < j#+l";
by (rtac (add_lt_mono1 RS lt_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat] 1));
by (EVERY [stac add_commute 1,
           stac add_commute 3,
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
by (blast_tac (le_cs addSIs [lt_mono,ford] addSEs [leE]) 1);
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
by (EVERY [stac add_commute 1,
           stac add_commute 3,
           rtac add_le_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
qed "add_le_mono";

(*** Monotonicity of Multiplication ***)

goal Arith.thy "!!i j k. [| i le j; j:nat; k:nat |] ==> i#*k le j#*k";
by (forward_tac [lt_nat_in_nat] 1);
by (nat_ind_tac "k" [] 2);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [add_le_mono])));
qed "mult_le_mono1";

(* le monotonicity, BOTH arguments*)
goal Arith.thy
    "!!i j k. [| i le j; k le l; j:nat; l:nat |] ==> i#*k le j#*l";
by (rtac (mult_le_mono1 RS le_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
by (EVERY [stac mult_commute 1,
           stac mult_commute 3,
           rtac mult_le_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0*)
goal Arith.thy "!!i j k. [| i<j; 0<k; j:nat; k:nat |] ==> k#*i < k#*j";
by (etac zero_lt_natE 1);
by (forward_tac [lt_nat_in_nat] 2);
by (ALLGOALS Asm_simp_tac);
by (nat_ind_tac "x" [] 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [add_lt_mono])));
qed "mult_lt_mono2";

goal Arith.thy "!!k. [| m: nat; n: nat |] ==> 0 < m#*n <-> 0<m & 0<n";
by (best_tac (!claset addEs [natE] addss (!simpset)) 1);
qed "zero_lt_mult_iff";

goal Arith.thy "!!k. [| m: nat; n: nat |] ==> m#*n = 1 <-> m=1 & n=1";
by (best_tac (!claset addEs [natE] unsafe_addss (!simpset)) 1);
qed "mult_eq_1_iff";

(*Cancellation law for division*)
goal Arith.thy
   "!!k. [| 0<n; 0<k; k:nat; m:nat; n:nat |] ==> (k#*m) div (k#*n) = m div n";
by (eres_inst_tac [("i","m")] complete_induct 1);
by (excluded_middle_tac "x<n" 1);
by (asm_simp_tac (!simpset addsimps [div_less, zero_lt_mult_iff, 
                                     mult_lt_mono2]) 2);
by (asm_full_simp_tac
     (!simpset addsimps [not_lt_iff_le, nat_into_Ord,
                         zero_lt_mult_iff, le_refl RS mult_le_mono, div_geq,
                         diff_mult_distrib2 RS sym,
                         div_termination RS ltD]) 1);
qed "div_cancel";

goal Arith.thy
   "!!k. [| 0<n; 0<k; k:nat; m:nat; n:nat |] ==> \
\        (k#*m) mod (k#*n) = k #* (m mod n)";
by (eres_inst_tac [("i","m")] complete_induct 1);
by (excluded_middle_tac "x<n" 1);
by (asm_simp_tac (!simpset addsimps [mod_less, zero_lt_mult_iff, 
                                     mult_lt_mono2]) 2);
by (asm_full_simp_tac
     (!simpset addsimps [not_lt_iff_le, nat_into_Ord,
                         zero_lt_mult_iff, le_refl RS mult_le_mono, mod_geq,
                         diff_mult_distrib2 RS sym,
                         div_termination RS ltD]) 1);
qed "mult_mod_distrib";

(** Lemma for gcd **)

val mono_lemma = (nat_into_Ord RS Ord_0_lt) RSN (2,mult_lt_mono2);

goal Arith.thy "!!m n. [| m = m#*n; m: nat; n: nat |] ==> n=1 | m=0";
by (rtac disjCI 1);
by (dtac sym 1);
by (rtac Ord_linear_lt 1 THEN REPEAT_SOME (ares_tac [nat_into_Ord,nat_1I]));
by (fast_tac (!claset unsafe_addss (!simpset)) 1);
by (fast_tac (le_cs addDs [mono_lemma] 
                    addss (!simpset addsimps [mult_1_right])) 1);
qed "mult_eq_self_implies_10";


(*Thanks to Sten Agerholm*)
goal Arith.thy  (* add_le_elim1 *)
    "!!m n k. [|m#+n le m#+k; m:nat; n:nat; k:nat|] ==> n le k";
by (etac rev_mp 1);
by (eres_inst_tac [("n","n")] nat_induct 1);
by (Asm_simp_tac 1);
by (Step_tac 1);
by (asm_full_simp_tac (!simpset addsimps [not_le_iff_lt,nat_into_Ord]) 1);
by (etac lt_asym 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (!simpset addsimps [le_iff, nat_into_Ord]) 1);
by (Blast_tac 1);
qed "add_le_elim1";

