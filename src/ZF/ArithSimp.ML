(*  Title:      ZF/ArithSimp.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Arithmetic with simplification
*)


Addsimprocs ArithData.nat_cancel;


(*** Difference ***)

Goal "m #- m = 0";
by (subgoal_tac "natify(m) #- natify(m) = 0" 1);
by (rtac (natify_in_nat RS nat_induct) 2);
by Auto_tac;
qed "diff_self_eq_0";

(**Addition is the inverse of subtraction**)

(*We need m:nat even if we replace the RHS by natify(m), for consider e.g.
  n=2, m=omega; then n + (m-n) = 2 + (0-2) = 2 ~= 0 = natify(m).*)
Goal "[| n le m;  m:nat |] ==> n #+ (m#-n) = m";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by Auto_tac;
qed "add_diff_inverse";

Goal "[| n le m;  m:nat |] ==> (m#-n) #+ n = m";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (asm_simp_tac (simpset() addsimps [add_commute, add_diff_inverse]) 1);
qed "add_diff_inverse2";

(*Proof is IDENTICAL to that of add_diff_inverse*)
Goal "[| n le m;  m:nat |] ==> succ(m) #- n = succ(m#-n)";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_succ";

Goal "[| m: nat; n: nat |] ==> 0 < (n #- m)   <->   m<n";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_diff";
Addsimps [zero_less_diff];


(** Difference distributes over multiplication **)

Goal "(m #- n) #* k = (m #* k) #- (n #* k)";
by (subgoal_tac "(natify(m) #- natify(n)) #* natify(k) = \
\                (natify(m) #* natify(k)) #- (natify(n) #* natify(k))" 1);
by (res_inst_tac [("m","natify(m)"),("n","natify(n)")] diff_induct 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [diff_cancel])));
qed "diff_mult_distrib" ;

Goal "k #* (m #- n) = (k #* m) #- (k #* n)";
by (simp_tac
    (simpset() addsimps [inst "m" "k" mult_commute, diff_mult_distrib]) 1);
qed "diff_mult_distrib2";


(*** Remainder ***)

(*We need m:nat even with natify*)
Goal "[| 0<n;  n le m;  m:nat |] ==> m #- n < m";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_le_self])));
qed "div_termination";

val div_rls =   (*for mod and div*)
    nat_typechecks @
    [Ord_transrec_type, apply_funtype, div_termination RS ltD,
     nat_into_Ord, not_lt_iff_le RS iffD1];

val div_ss = simpset() addsimps [div_termination RS ltD,
				 not_lt_iff_le RS iffD2];

Goalw [raw_mod_def] "[| m:nat;  n:nat |] ==> raw_mod (m, n) : nat";
by (rtac Ord_transrec_type 1);
by (auto_tac(claset(), simpset() addsimps [nat_into_Ord RS Ord_0_lt_iff]));
by (REPEAT (ares_tac div_rls 1));
qed "raw_mod_type";

Goalw [mod_def] "m mod n : nat";
by (simp_tac (simpset() addsimps [mod_def, raw_mod_type]) 1);
qed "mod_type";
AddTCs [mod_type];
AddIffs [mod_type];


(** Aribtrary definitions for division by zero.  Useful to simplify 
    certain equations **)

Goalw [div_def] "a div 0 = 0";
by (rtac (raw_div_def RS def_transrec RS trans) 1);
by (Asm_simp_tac 1);
qed "DIVISION_BY_ZERO_DIV";  (*NOT for adding to default simpset*)

Goalw [mod_def] "a mod 0 = natify(a)";
by (rtac (raw_mod_def RS def_transrec RS trans) 1);
by (Asm_simp_tac 1);
qed "DIVISION_BY_ZERO_MOD";  (*NOT for adding to default simpset*)

fun div_undefined_case_tac s i =
  case_tac s i THEN 
  asm_full_simp_tac
         (simpset() addsimps [nat_into_Ord RS Ord_0_lt_iff]) (i+1) THEN
  asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO_DIV, 
				    DIVISION_BY_ZERO_MOD]) i;

Goal "m<n ==> raw_mod (m,n) = m";
by (rtac (raw_mod_def RS def_transrec RS trans) 1);
by (asm_simp_tac (simpset() addsimps [div_termination RS ltD]) 1);
qed "raw_mod_less";

Goal "[| m<n; n : nat |] ==> m mod n = m";
by (ftac lt_nat_in_nat 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [mod_def, raw_mod_less]) 1);
qed "mod_less";

Goal "[| 0<n; n le m;  m:nat |] ==> raw_mod (m, n) = raw_mod (m#-n, n)";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (rtac (raw_mod_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
by (Blast_tac 1);
qed "raw_mod_geq";

Goal "[| n le m;  m:nat |] ==> m mod n = (m#-n) mod n";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (div_undefined_case_tac "n=0" 1);
by (asm_simp_tac (simpset() addsimps [mod_def, raw_mod_geq]) 1);
qed "mod_geq";

Addsimps [mod_less];


(*** Division ***)

Goalw [raw_div_def] "[| m:nat;  n:nat |] ==> raw_div (m, n) : nat";
by (rtac Ord_transrec_type 1);
by (auto_tac(claset(), simpset() addsimps [nat_into_Ord RS Ord_0_lt_iff]));
by (REPEAT (ares_tac div_rls 1));
qed "raw_div_type";

Goalw [div_def] "m div n : nat";
by (simp_tac (simpset() addsimps [div_def, raw_div_type]) 1);
qed "div_type";
AddTCs [div_type];
AddIffs [div_type];

Goal "m<n ==> raw_div (m,n) = 0";
by (rtac (raw_div_def RS def_transrec RS trans) 1);
by (asm_simp_tac (simpset() addsimps [div_termination RS ltD]) 1);
qed "raw_div_less";

Goal "[| m<n; n : nat |] ==> m div n = 0";
by (ftac lt_nat_in_nat 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [div_def, raw_div_less]) 1);
qed "div_less";

Goal "[| 0<n;  n le m;  m:nat |] ==> raw_div(m,n) = succ(raw_div(m#-n, n))";
by (subgoal_tac "n ~= 0" 1);
by (Blast_tac 2);
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (rtac (raw_div_def RS def_transrec RS trans) 1);
by (asm_simp_tac div_ss 1);
qed "raw_div_geq";

Goal "[| 0<n;  n le m;  m:nat |] ==> m div n = succ ((m#-n) div n)";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (asm_simp_tac (simpset() addsimps [div_def, raw_div_geq]) 1);
qed "div_geq";

Addsimps [div_less, div_geq];


(*A key result*)
Goal "[| m: nat;  n: nat |] ==> (m div n)#*n #+ m mod n = m";
by (div_undefined_case_tac "n=0" 1);
by (etac complete_induct 1);
by (case_tac "x<n" 1);
(*case n le x*)
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, add_assoc, mod_geq,
                         div_termination RS ltD, add_diff_inverse]) 2);
(*case x<n*)
by (Asm_simp_tac 1);
val lemma = result();

Goal "(m div n)#*n #+ m mod n = natify(m)";
by (subgoal_tac
    "(natify(m) div natify(n))#*natify(n) #+ natify(m) mod natify(n) = \
\    natify(m)" 1);
by (stac lemma 2);
by Auto_tac;
qed "mod_div_equality_natify";

Goal "m: nat ==> (m div n)#*n #+ m mod n = m";
by (asm_simp_tac (simpset() addsimps [mod_div_equality_natify]) 1);
qed "mod_div_equality";


(*** Further facts about mod (mainly for mutilated chess board) ***)

Goal "[| 0<n;  m:nat;  n:nat |] \
\     ==> succ(m) mod n = (if succ(m mod n) = n then 0 else succ(m mod n))";
by (etac complete_induct 1);
by (excluded_middle_tac "succ(x)<n" 1);
(* case succ(x) < n *)
by (asm_simp_tac (simpset() addsimps [nat_le_refl RS lt_trans, 
				      succ_neq_self]) 2);
by (asm_simp_tac (simpset() addsimps [ltD RS mem_imp_not_eq]) 2);
(* case n le succ(x) *)
by (asm_full_simp_tac (simpset() addsimps [mod_geq, not_lt_iff_le]) 1);
by (etac leE 1);
(*equality case*)
by (asm_full_simp_tac (simpset() addsimps [diff_self_eq_0]) 2);
by (asm_simp_tac (simpset() addsimps [mod_geq, div_termination RS ltD, 
				      diff_succ]) 1);
val lemma = result();

Goal "n:nat ==> \
\     succ(m) mod n = (if succ(m mod n) = n then 0 else succ(m mod n))";
by (case_tac "n=0" 1);
by (asm_simp_tac (simpset() addsimps [natify_succ, DIVISION_BY_ZERO_MOD]) 1);
by (subgoal_tac
    "natify(succ(m)) mod n = \
\      (if succ(natify(m) mod n) = n then 0 else succ(natify(m) mod n))" 1);
by (stac natify_succ 2);
by (rtac lemma 2);
by (auto_tac(claset(), 
	     simpset() delsimps [natify_succ] 
             addsimps [nat_into_Ord RS Ord_0_lt_iff]));
qed "mod_succ";

Goal "[| 0<n;  n:nat |] ==> m mod n < n";
by (subgoal_tac "natify(m) mod n < n" 1);
by (res_inst_tac [("i","natify(m)")] complete_induct 2);
by (case_tac "x<n" 3);
(*case x<n*)
by (Asm_simp_tac 3);
(*case n le x*)
by (asm_full_simp_tac
     (simpset() addsimps [mod_geq, not_lt_iff_le, div_termination RS ltD]) 3);
by Auto_tac;
qed "mod_less_divisor";

Goal "b<2 ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)";
by (subgoal_tac "k mod 2: 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor RS ltD]) 2);
by (dtac ltD 1);
by Auto_tac;
qed "mod2_cases";

Goal "succ(succ(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2: 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor RS ltD]) 2);
by (auto_tac (claset(), simpset() addsimps [mod_succ]));  
qed "mod2_succ_succ";

Addsimps [mod2_succ_succ];

Goal "(m#+m#+n) mod 2 = n mod 2";
by (subgoal_tac "(natify(m)#+natify(m)#+n) mod 2 = n mod 2" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by Auto_tac;
qed "mod2_add_more";

Goal "(m#+m) mod 2 = 0";
by (cut_inst_tac [("n","0")] mod2_add_more 1);
by Auto_tac;
qed "mod2_add_self";

Addsimps [mod2_add_more, mod2_add_self];


(**** Additional theorems about "le" ****)

Goal "m:nat ==> m le (m #+ n)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_le_self";

Goal "m:nat ==> m le (n #+ m)";
by (stac add_commute 1);
by (etac add_le_self 1);
qed "add_le_self2";

(*** Monotonicity of Multiplication ***)

Goal "[| i le j; j:nat |] ==> (i#*k) le (j#*k)";
by (subgoal_tac "natify(i)#*natify(k) le j#*natify(k)" 1);
by (ftac lt_nat_in_nat 2);
by (res_inst_tac [("n","natify(k)")] nat_induct 3);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_le_mono])));
qed "mult_le_mono1";

(* le monotonicity, BOTH arguments*)
Goal "[| i le j; k le l; j:nat; l:nat |] ==> i#*k le j#*l";
by (rtac (mult_le_mono1 RS le_trans) 1);
by (REPEAT (assume_tac 1));
by (EVERY [stac mult_commute 1,
           stac mult_commute 1,
           rtac mult_le_mono1 1]);
by (REPEAT (assume_tac 1));
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0.
  I can't see how to relax the typing conditions.*)
Goal "[| i<j; 0<k; j:nat; k:nat |] ==> k#*i < k#*j";
by (etac zero_lt_natE 1);
by (ftac lt_nat_in_nat 2);
by (ALLGOALS Asm_simp_tac);
by (induct_tac "x" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_lt_mono])));
qed "mult_lt_mono2";

Goal "[| i<j; 0<k; j:nat; k:nat |] ==> i#*k < j#*k";
by (asm_simp_tac (simpset() addsimps [mult_lt_mono2, 
				      inst "n" "k" mult_commute]) 1);
qed "mult_lt_mono1";

Goal "m#+n = 0 <-> natify(m)=0 & natify(n)=0";
by (subgoal_tac "natify(m) #+ natify(n) = 0 <-> natify(m)=0 & natify(n)=0" 1);
by (res_inst_tac [("n","natify(m)")] natE 2);
 by (res_inst_tac [("n","natify(n)")] natE 4);
by Auto_tac;  
qed "add_eq_0_iff";
AddIffs [add_eq_0_iff];

Goal "0 < m#*n <-> 0 < natify(m) & 0 < natify(n)";
by (subgoal_tac "0 < natify(m)#*natify(n) <-> \
\                0 < natify(m) & 0 < natify(n)" 1);
by (res_inst_tac [("n","natify(m)")] natE 2);
 by (res_inst_tac [("n","natify(n)")] natE 4);
  by (res_inst_tac [("n","natify(n)")] natE 3);
by Auto_tac;  
qed "zero_lt_mult_iff";

Goal "m#*n = 1 <-> natify(m)=1 & natify(n)=1";
by (subgoal_tac "natify(m) #* natify(n) = 1 <-> natify(m)=1 & natify(n)=1" 1);
by (res_inst_tac [("n","natify(m)")] natE 2);
 by (res_inst_tac [("n","natify(n)")] natE 4);
by Auto_tac;  
qed "mult_eq_1_iff";
AddIffs [zero_lt_mult_iff, mult_eq_1_iff];


(** Cancellation laws for common factors in comparisons **)

Goal "[| k: nat; m: nat; n: nat |] ==> (m#*k < n#*k) <-> (0<k & m<n)";
by (safe_tac (claset() addSIs [mult_lt_mono1]));
by (etac natE 1);
by Auto_tac;  
by (rtac (not_le_iff_lt RS iffD1) 1); 
by (dtac (not_le_iff_lt RSN (2,rev_iffD2)) 3); 
by (blast_tac (claset() addIs [mult_le_mono1]) 5); 
by Auto_tac;  
val lemma = result();

Goal "(m#*k < n#*k) <-> (0 < natify(k) & natify(m) < natify(n))";
by (rtac iff_trans 1);
by (rtac lemma 2);
by Auto_tac;  
qed "mult_less_cancel2";

Goal "(k#*m < k#*n) <-> (0 < natify(k) & natify(m) < natify(n))";
by (simp_tac (simpset() addsimps [mult_less_cancel2, 
                                  inst "m" "k" mult_commute]) 1);
qed "mult_less_cancel1";
Addsimps [mult_less_cancel1, mult_less_cancel2];

Goal "(m#*k le n#*k) <-> (0 < natify(k) --> natify(m) le natify(n))";
by (asm_simp_tac (simpset() addsimps [not_lt_iff_le RS iff_sym]) 1);
by Auto_tac;  
qed "mult_le_cancel2";

Goal "(k#*m le k#*n) <-> (0 < natify(k) --> natify(m) le natify(n))";
by (asm_simp_tac (simpset() addsimps [not_lt_iff_le RS iff_sym]) 1);
by Auto_tac;  
qed "mult_le_cancel1";
Addsimps [mult_le_cancel1, mult_le_cancel2];

Goal "[| Ord(m); Ord(n) |] ==> m=n <-> (m le n & n le m)";
by (blast_tac (claset() addIs [le_anti_sym]) 1); 
qed "Ord_eq_iff_le";

Goal "[| k: nat; m: nat; n: nat |] ==> (m#*k = n#*k) <-> (m=n | k=0)";
by (asm_simp_tac (simpset() addsimps [inst "m" "m#*k" Ord_eq_iff_le,
                                      inst "m" "m" Ord_eq_iff_le]) 1); 
by (auto_tac (claset(), simpset() addsimps [Ord_0_lt_iff]));  
val lemma = result();

Goal "(m#*k = n#*k) <-> (natify(m) = natify(n) | natify(k) = 0)";
by (rtac iff_trans 1);
by (rtac lemma 2);
by Auto_tac;  
qed "mult_cancel2";

Goal "(k#*m = k#*n) <-> (natify(m) = natify(n) | natify(k) = 0)";
by (simp_tac (simpset() addsimps [mult_cancel2, inst "m" "k" mult_commute]) 1);
qed "mult_cancel1";
Addsimps [mult_cancel1, mult_cancel2];


(*Cancellation law for division*)
Goal "[| 0<n; 0<k; k:nat; m:nat; n:nat |] ==> (k#*m) div (k#*n) = m div n";
by (eres_inst_tac [("i","m")] complete_induct 1);
by (excluded_middle_tac "x<n" 1);
by (asm_simp_tac (simpset() addsimps [div_less, zero_lt_mult_iff, 
                                     mult_lt_mono2]) 2);
by (asm_full_simp_tac
     (simpset() addsimps [not_lt_iff_le, 
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
     (simpset() addsimps [not_lt_iff_le, 
                         zero_lt_mult_iff, le_refl RS mult_le_mono, mod_geq,
                         diff_mult_distrib2 RS sym,
                         div_termination RS ltD]) 1);
qed "mult_mod_distrib";

(*Lemma for gcd*)
Goal "m = m#*n ==> natify(n)=1 | m=0";
by (subgoal_tac "m: nat" 1);
by (etac ssubst 2);
by (rtac disjCI 1);
by (dtac sym 1);
by (rtac Ord_linear_lt 1 THEN REPEAT_SOME (ares_tac [nat_into_Ord,nat_1I]));
by (dtac (nat_into_Ord RS Ord_0_lt RSN (2,mult_lt_mono2)) 3);
by Auto_tac;
by (subgoal_tac "m #* n = 0" 1);
by (stac (mult_natify2 RS sym) 2);
by (auto_tac (claset(), simpset() delsimps [mult_natify2]));  
qed "mult_eq_self_implies_10";

Goal "[| m<n; n: nat |] ==> EX k: nat. n = succ(m#+k)";
by (ftac lt_nat_in_nat 1 THEN assume_tac 1);
by (etac rev_mp 1);
by (induct_tac "n" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [le_iff])));
by (blast_tac (claset() addSEs [leE] 
                        addSIs [add_0_right RS sym, add_succ_right RS sym]) 1);
qed_spec_mp "less_imp_succ_add";



