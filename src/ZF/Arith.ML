(*  Title:      ZF/Arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Arithmetic operators and their definitions

Proofs about elementary arithmetic: addition, multiplication, etc.
*)

(*"Difference" is subtraction of natural numbers.
  There are no negative numbers; we have
     m #- n = 0  iff  m<=n   and     m #- n = succ(k) iff m>n.
  Also, rec(m, 0, %z w.z) is pred(m).   
*)

Addsimps [rec_type, nat_0_le, nat_le_refl];
val nat_typechecks = [rec_type, nat_0I, nat_1I, nat_succI, Ord_nat];

Goal "[| 0<k; k: nat |] ==> EX j: nat. k = succ(j)";
by (etac rev_mp 1);
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Blast_tac 1);
val lemma = result();

(* [| 0 < k; k: nat; !!j. [| j: nat; k = succ(j) |] ==> Q |] ==> Q *)
bind_thm ("zero_lt_natE", lemma RS bexE);


(** Addition **)

Goal "[| m:nat;  n:nat |] ==> m #+ n : nat";
by (induct_tac "m" 1);
by Auto_tac;
qed "add_type";
Addsimps [add_type];
AddTCs [add_type];

(** Multiplication **)

Goal "[| m:nat;  n:nat |] ==> m #* n : nat";
by (induct_tac "m" 1);
by Auto_tac;
qed "mult_type";
Addsimps [mult_type];
AddTCs [mult_type];


(** Difference **)

Goal "[| m:nat;  n:nat |] ==> m #- n : nat";
by (induct_tac "n" 1);
by Auto_tac;
by (fast_tac (claset() addIs [nat_case_type]) 1);
qed "diff_type";
Addsimps [diff_type];
AddTCs [diff_type];

Goal "n:nat ==> 0 #- n = 0";
by (induct_tac "n" 1);
by Auto_tac;
qed "diff_0_eq_0";

(*Must simplify BEFORE the induction: else we get a critical pair*)
Goal "[| m:nat;  n:nat |] ==> succ(m) #- succ(n) = m #- n";
by (Asm_simp_tac 1);
by (induct_tac "n" 1);
by Auto_tac;
qed "diff_succ_succ";

Addsimps [diff_0_eq_0, diff_succ_succ];

(*This defining property is no longer wanted*)
Delsimps [diff_SUCC];  

val prems = goal Arith.thy 
    "[| m:nat;  n:nat |] ==> m #- n le m";
by (rtac (prems MRS diff_induct) 1);
by (etac leE 3);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps prems @ [le_iff, nat_into_Ord])));
qed "diff_le_self";

(*** Simplification over add, mult, diff ***)

val arith_typechecks = [add_type, mult_type, diff_type];


(*** Addition ***)

(*Associative law for addition*)
Goal "m:nat ==> (m #+ n) #+ k = m #+ (n #+ k)";
by (induct_tac "m" 1);
by Auto_tac;
qed "add_assoc";

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
Goal "m:nat ==> m #+ 0 = m";
by (induct_tac "m" 1);
by Auto_tac;
qed "add_0_right";

Goal "m:nat ==> m #+ succ(n) = succ(m #+ n)";
by (induct_tac "m" 1);
by Auto_tac;
qed "add_succ_right";

Addsimps [add_0_right, add_succ_right];

(*Commutative law for addition*)  
Goal "[| m:nat;  n:nat |] ==> m #+ n = n #+ m";
by (induct_tac "n" 1);
by Auto_tac;
qed "add_commute";

(*for a/c rewriting*)
Goal "[| m:nat;  n:nat |] ==> m#+(n#+k)=n#+(m#+k)";
by (asm_simp_tac (simpset() addsimps [add_assoc RS sym, add_commute]) 1);
qed "add_left_commute";

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

(*Cancellation law on the left*)
Goal "[| k #+ m = k #+ n;  k:nat |] ==> m=n";
by (etac rev_mp 1);
by (induct_tac "k" 1);
by Auto_tac;
qed "add_left_cancel";

(*** Multiplication ***)

(*right annihilation in product*)
Goal "m:nat ==> m #* 0 = 0";
by (induct_tac "m" 1);
by Auto_tac;
qed "mult_0_right";

(*right successor law for multiplication*)
Goal "[| m:nat;  n:nat |] ==> m #* succ(n) = m #+ (m #* n)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps add_ac)));
qed "mult_succ_right";

Addsimps [mult_0_right, mult_succ_right];

Goal "n:nat ==> 1 #* n = n";
by (Asm_simp_tac 1);
qed "mult_1";

Goal "n:nat ==> n #* 1 = n";
by (Asm_simp_tac 1);
qed "mult_1_right";

Addsimps [mult_1, mult_1_right];

(*Commutative law for multiplication*)
Goal "[| m:nat;  n:nat |] ==> m #* n = n #* m";
by (induct_tac "m" 1);
by Auto_tac;
qed "mult_commute";

(*addition distributes over multiplication*)
Goal "[| m:nat;  k:nat |] ==> (m #+ n) #* k = (m #* k) #+ (n #* k)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_assoc RS sym])));
qed "add_mult_distrib";

(*Distributive law on the left; requires an extra typing premise*)
Goal "[| m:nat;  n:nat;  k:nat |] ==> k #* (m #+ n) = (k #* m) #+ (k #* n)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps add_ac)));
qed "add_mult_distrib_left";

(*Associative law for multiplication*)
Goal "[| m:nat;  n:nat;  k:nat |] ==> (m #* n) #* k = m #* (n #* k)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_mult_distrib])));
qed "mult_assoc";

(*for a/c rewriting*)
Goal "[| m:nat;  n:nat;  k:nat |] ==> m #* (n #* k) = n #* (m #* k)";
by (rtac (mult_commute RS trans) 1);
by (rtac (mult_assoc RS trans) 3);
by (rtac (mult_commute RS subst_context) 6);
by (REPEAT (ares_tac [mult_type] 1));
qed "mult_left_commute";

val mult_ac = [mult_assoc,mult_commute,mult_left_commute];


(*** Difference ***)

Goal "m:nat ==> m #- m = 0";
by (induct_tac "m" 1);
by Auto_tac;
qed "diff_self_eq_0";

(*Addition is the inverse of subtraction*)
Goal "[| n le m;  m:nat |] ==> n #+ (m#-n) = m";
by (ftac lt_nat_in_nat 1);
by (etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "add_diff_inverse";

Goal "[| n le m;  m:nat |] ==> (m#-n) #+ n = m";
by (ftac lt_nat_in_nat 1);
by (etac nat_succI 1);
by (asm_simp_tac (simpset() addsimps [add_commute, add_diff_inverse]) 1);
qed "add_diff_inverse2";

(*Proof is IDENTICAL to that above*)
Goal "[| n le m;  m:nat |] ==> succ(m) #- n = succ(m#-n)";
by (ftac lt_nat_in_nat 1);
by (etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_succ";

Goal "[| m: nat; n: nat |] ==> 0 < n #- m  <->  m<n";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_diff";
Addsimps [zero_less_diff];


(** Subtraction is the inverse of addition. **)

Goal "[| m:nat;  n:nat |] ==> (n#+m) #- n = m";
by (induct_tac "n" 1);
by Auto_tac;
qed "diff_add_inverse";

Goal "[| m:nat;  n:nat |] ==> (m#+n) #- n = m";
by (res_inst_tac [("m1","m")] (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [diff_add_inverse] 1));
qed "diff_add_inverse2";

Goal "[| k:nat; m: nat; n: nat |] ==> (k#+m) #- (k#+n) = m #- n";
by (induct_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_cancel";

Goal "[| k:nat; m: nat; n: nat |] ==> (m#+k) #- (n#+k) = m #- n";
val add_commute_k = read_instantiate [("n","k")] add_commute;
by (asm_simp_tac (simpset() addsimps [add_commute_k, diff_cancel]) 1);
qed "diff_cancel2";

Goal "[| m:nat;  n:nat |] ==> n #- (n#+m) = 0";
by (induct_tac "n" 1);
by Auto_tac;
qed "diff_add_0";

(** Difference distributes over multiplication **)

Goal "[| m:nat; n: nat; k:nat |] ==> (m #- n) #* k = (m #* k) #- (n #* k)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_cancel])));
qed "diff_mult_distrib" ;

Goal "[| m:nat; n: nat; k:nat |] ==> k #* (m #- n) = (k #* m) #- (k #* n)";
val mult_commute_k = read_instantiate [("m","k")] mult_commute;
by (asm_simp_tac (simpset() addsimps 
                  [mult_commute_k, diff_mult_distrib]) 1);
qed "diff_mult_distrib2" ;

(*** Remainder ***)

Goal "[| 0<n;  n le m;  m:nat |] ==> m #- n < m";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_le_self])));
qed "div_termination";

val div_rls =   (*for mod and div*)
    nat_typechecks @
    [Ord_transrec_type, apply_type, div_termination RS ltD, if_type,
     nat_into_Ord, not_lt_iff_le RS iffD1];

val div_ss = simpset() addsimps [nat_into_Ord, div_termination RS ltD,
				 not_lt_iff_le RS iffD2];

(*Type checking depends upon termination!*)
Goalw [mod_def] "[| 0<n;  m:nat;  n:nat |] ==> m mod n : nat";
by (REPEAT (ares_tac div_rls 1 ORELSE etac lt_trans 1));
qed "mod_type";
AddTCs [mod_type];

Goal "[| 0<n;  m<n |] ==> m mod n = m";
by (rtac (mod_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "mod_less";

Goal "[| 0<n;  n le m;  m:nat |] ==> m mod n = (m#-n) mod n";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (rtac (mod_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "mod_geq";

Addsimps [mod_type, mod_less, mod_geq];

(*** Quotient ***)

(*Type checking depends upon termination!*)
Goalw [div_def]
    "[| 0<n;  m:nat;  n:nat |] ==> m div n : nat";
by (REPEAT (ares_tac div_rls 1 ORELSE etac lt_trans 1));
qed "div_type";
AddTCs [div_type];

Goal "[| 0<n;  m<n |] ==> m div n = 0";
by (rtac (div_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "div_less";

Goal "[| 0<n;  n le m;  m:nat |] ==> m div n = succ((m#-n) div n)";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (rtac (div_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "div_geq";

Addsimps [div_type, div_less, div_geq];

(*A key result*)
Goal "[| 0<n;  m:nat;  n:nat |] ==> (m div n)#*n #+ m mod n = m";
by (etac complete_induct 1);
by (excluded_middle_tac "x<n" 1);
(*case x<n*)
by (Asm_simp_tac 2);
(*case n le x*)
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, nat_into_Ord, add_assoc,
                         div_termination RS ltD, add_diff_inverse]) 1);
qed "mod_div_equality";


(*** Further facts about mod (mainly for mutilated chess board) ***)

Goal "[| 0<n;  m:nat;  n:nat |] \
\     ==> succ(m) mod n = (if succ(m mod n) = n then 0 else succ(m mod n))";
by (etac complete_induct 1);
by (excluded_middle_tac "succ(x)<n" 1);
(* case succ(x) < n *)
by (asm_simp_tac (simpset() addsimps [mod_less, nat_le_refl RS lt_trans,
                                     succ_neq_self]) 2);
by (asm_simp_tac (simpset() addsimps [ltD RS mem_imp_not_eq]) 2);
(* case n le succ(x) *)
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, nat_into_Ord, mod_geq]) 1);
by (etac leE 1);
by (asm_simp_tac (simpset() addsimps [div_termination RS ltD, diff_succ, 
                                     mod_geq]) 1);
by (asm_simp_tac (simpset() addsimps [mod_less, diff_self_eq_0]) 1);
qed "mod_succ";

Goal "[| 0<n;  m:nat;  n:nat |] ==> m mod n < n";
by (etac complete_induct 1);
by (excluded_middle_tac "x<n" 1);
(*case x<n*)
by (asm_simp_tac (simpset() addsimps [mod_less]) 2);
(*case n le x*)
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, nat_into_Ord,
                         mod_geq, div_termination RS ltD]) 1);
qed "mod_less_divisor";


Goal "[| k: nat; b<2 |] ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)";
by (subgoal_tac "k mod 2: 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor RS ltD]) 2);
by (dtac ltD 1);
by Auto_tac;
qed "mod2_cases";

Goal "m:nat ==> succ(succ(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2: 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor RS ltD]) 2);
by (asm_simp_tac (simpset() addsimps [mod_succ] setloop Step_tac) 1);
qed "mod2_succ_succ";

Goal "m:nat ==> (m#+m) mod 2 = 0";
by (induct_tac "m" 1);
by (simp_tac (simpset() addsimps [mod_less]) 1);
by (asm_simp_tac (simpset() addsimps [mod2_succ_succ, add_succ_right]) 1);
qed "mod2_add_self";


(**** Additional theorems about "le" ****)

Goal "[| m:nat;  n:nat |] ==> m le m #+ n";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_le_self";

Goal "[| m:nat;  n:nat |] ==> m le n #+ m";
by (stac add_commute 1);
by (REPEAT (ares_tac [add_le_self] 1));
qed "add_le_self2";

(*** Monotonicity of Addition ***)

(*strict, in 1st argument; proof is by rule induction on 'less than'*)
Goal "[| i<j; j:nat; k:nat |] ==> i#+k < j#+k";
by (ftac lt_nat_in_nat 1);
by (assume_tac 1);
by (etac succ_lt_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [leI])));
qed "add_lt_mono1";

(*strict, in both arguments*)
Goal "[| i<j; k<l; j:nat; l:nat |] ==> i#+k < j#+l";
by (rtac (add_lt_mono1 RS lt_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat] 1));
by (EVERY [stac add_commute 1,
           stac add_commute 3,
           rtac add_lt_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat] 1));
qed "add_lt_mono";

(*A [clumsy] way of lifting < monotonicity to le monotonicity *)
val lt_mono::ford::prems = Goal
     "[| !!i j. [| i<j; j:k |] ==> f(i) < f(j); \
\        !!i. i:k ==> Ord(f(i));                \
\        i le j;  j:k                           \
\     |] ==> f(i) le f(j)";
by (cut_facts_tac prems 1);
by (blast_tac (le_cs addSIs [lt_mono,ford] addSEs [leE]) 1);
qed "Ord_lt_mono_imp_le_mono";

(*le monotonicity, 1st argument*)
Goal "[| i le j; j:nat; k:nat |] ==> i#+k le j#+k";
by (res_inst_tac [("f", "%j. j#+k")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [add_lt_mono1, add_type RS nat_into_Ord] 1));
qed "add_le_mono1";

(* le monotonicity, BOTH arguments*)
Goal "[| i le j; k le l; j:nat; l:nat |] ==> i#+k le j#+l";
by (rtac (add_le_mono1 RS le_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
by (EVERY [stac add_commute 1,
           stac add_commute 3,
           rtac add_le_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
qed "add_le_mono";

(*** Monotonicity of Multiplication ***)

Goal "[| i le j; j:nat; k:nat |] ==> i#*k le j#*k";
by (ftac lt_nat_in_nat 1);
by (induct_tac "k" 2);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_le_mono])));
qed "mult_le_mono1";

(* le monotonicity, BOTH arguments*)
Goal "[| i le j; k le l; j:nat; l:nat |] ==> i#*k le j#*l";
by (rtac (mult_le_mono1 RS le_trans) 1);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
by (EVERY [stac mult_commute 1,
           stac mult_commute 3,
           rtac mult_le_mono1 5]);
by (REPEAT (eresolve_tac [asm_rl, lt_nat_in_nat, nat_succI] 1));
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0*)
Goal "[| i<j; 0<k; j:nat; k:nat |] ==> k#*i < k#*j";
by (etac zero_lt_natE 1);
by (ftac lt_nat_in_nat 2);
by (ALLGOALS Asm_simp_tac);
by (induct_tac "x" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_lt_mono])));
qed "mult_lt_mono2";

Goal "[| i<j; 0<c; i:nat; j:nat; c:nat |] ==> i#*c < j#*c";
by (asm_simp_tac (simpset() addsimps [mult_lt_mono2, mult_commute]) 1);
qed "mult_lt_mono1";

Goal "[| m: nat; n: nat |] ==> 0 < m#*n <-> 0<m & 0<n";
by (best_tac (claset() addEs [natE] addss (simpset())) 1);
qed "zero_lt_mult_iff";

Goal "[| m: nat; n: nat |] ==> m#*n = 1 <-> m=1 & n=1";
by (best_tac (claset() addEs [natE] addss (simpset())) 1);
qed "mult_eq_1_iff";

(*Cancellation law for division*)
Goal "[| 0<n; 0<k; k:nat; m:nat; n:nat |] ==> (k#*m) div (k#*n) = m div n";
by (eres_inst_tac [("i","m")] complete_induct 1);
by (excluded_middle_tac "x<n" 1);
by (asm_simp_tac (simpset() addsimps [div_less, zero_lt_mult_iff, 
                                     mult_lt_mono2]) 2);
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, nat_into_Ord,
                         zero_lt_mult_iff, le_refl RS mult_le_mono, div_geq,
                         diff_mult_distrib2 RS sym,
                         div_termination RS ltD]) 1);
qed "div_cancel";

Goal "[| 0<n; 0<k; k:nat; m:nat; n:nat |] ==> \
\        (k#*m) mod (k#*n) = k #* (m mod n)";
by (eres_inst_tac [("i","m")] complete_induct 1);
by (excluded_middle_tac "x<n" 1);
by (asm_simp_tac (simpset() addsimps [mod_less, zero_lt_mult_iff, 
                                     mult_lt_mono2]) 2);
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, nat_into_Ord,
                         zero_lt_mult_iff, le_refl RS mult_le_mono, mod_geq,
                         diff_mult_distrib2 RS sym,
                         div_termination RS ltD]) 1);
qed "mult_mod_distrib";

(*Lemma for gcd*)
Goal "[| m = m#*n; m: nat; n: nat |] ==> n=1 | m=0";
by (rtac disjCI 1);
by (dtac sym 1);
by (rtac Ord_linear_lt 1 THEN REPEAT_SOME (ares_tac [nat_into_Ord,nat_1I]));
by (dtac (nat_into_Ord RS Ord_0_lt RSN (2,mult_lt_mono2)) 2);
by Auto_tac;
qed "mult_eq_self_implies_10";

(*Thanks to Sten Agerholm*)
Goal "[|m#+n le m#+k; m:nat; n:nat; k:nat|] ==> n le k";
by (etac rev_mp 1);
by (induct_tac "m" 1);
by (Asm_simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [not_le_iff_lt,nat_into_Ord]) 1);
qed "add_le_elim1";

Goal "[| m<n; n: nat |] ==> EX k: nat. n = succ(m#+k)";
by (ftac lt_nat_in_nat 1 THEN assume_tac 1);
by (etac rev_mp 1);
by (induct_tac "n" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [le_iff])));
by (blast_tac (claset() addSEs [leE] 
                        addSIs [add_0_right RS sym, add_succ_right RS sym]) 1);
qed_spec_mp "less_imp_Suc_add";
