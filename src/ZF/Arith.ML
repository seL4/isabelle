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

Addsimps [rec_type, nat_0_le];
bind_thms ("nat_typechecks", [rec_type, nat_0I, nat_1I, nat_succI, Ord_nat]);

Goal "[| 0<k; k: nat |] ==> EX j: nat. k = succ(j)";
by (etac rev_mp 1);
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Blast_tac 1);
val lemma = result();

(* [| 0 < k; k: nat; !!j. [| j: nat; k = succ(j) |] ==> Q |] ==> Q *)
bind_thm ("zero_lt_natE", lemma RS bexE);


(** natify: coercion to "nat" **)

Goalw [pred_def] "pred(succ(y)) = y";
by Auto_tac;  
qed "pred_succ_eq";
Addsimps [pred_succ_eq];

Goal "natify(succ(x)) = succ(natify(x))";
by (rtac (natify_def RS def_Vrecursor RS trans) 1);
by Auto_tac;  
qed "natify_succ";

Goal "natify(0) = 0";
by (rtac (natify_def RS def_Vrecursor RS trans) 1);
by Auto_tac;  
qed "natify_0";
Addsimps [natify_0];

Goal "ALL z. x ~= succ(z) ==> natify(x) = 0";
by (rtac (natify_def RS def_Vrecursor RS trans) 1);
by Auto_tac;  
qed "natify_non_succ";

Goal "natify(x) : nat";
by (eps_ind_tac "x" 1);
by (case_tac "EX z. x1 = succ(z)" 1);
by (auto_tac (claset(), simpset() addsimps [natify_succ, natify_non_succ]));  
qed "natify_in_nat";
AddIffs [natify_in_nat];
AddTCs [natify_in_nat];

Goal "n : nat ==> natify(n) = n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [natify_succ]));  
qed "natify_ident";
Addsimps [natify_ident];

Goal "[|natify(x) = y;  x: nat|] ==> x=y";
by Auto_tac; 
qed "natify_eqE";


(*** Collapsing rules: to remove natify from arithmetic expressions ***)

Goal "natify(natify(x)) = natify(x)";
by (Simp_tac 1);
qed "natify_idem";
Addsimps [natify_idem];

(** Addition **)

Goal "natify(m) #+ n = m #+ n";
by (simp_tac (simpset() addsimps [add_def]) 1);
qed "add_natify1";

Goal "m #+ natify(n) = m #+ n";
by (simp_tac (simpset() addsimps [add_def]) 1);
qed "add_natify2";
Addsimps [add_natify1, add_natify2];

(** Multiplication **)

Goal "natify(m) #* n = m #* n";
by (simp_tac (simpset() addsimps [mult_def]) 1);
qed "mult_natify1";

Goal "m #* natify(n) = m #* n";
by (simp_tac (simpset() addsimps [mult_def]) 1);
qed "mult_natify2";
Addsimps [mult_natify1, mult_natify2];

(** Difference **)

Goal "natify(m) #- n = m #- n";
by (simp_tac (simpset() addsimps [diff_def]) 1);
qed "diff_natify1";

Goal "m #- natify(n) = m #- n";
by (simp_tac (simpset() addsimps [diff_def]) 1);
qed "diff_natify2";
Addsimps [diff_natify1, diff_natify2];

(** Remainder **)

Goal "natify(m) mod n = m mod n";
by (simp_tac (simpset() addsimps [mod_def]) 1);
qed "mod_natify1";

Goal "m mod natify(n) = m mod n";
by (simp_tac (simpset() addsimps [mod_def]) 1);
qed "mod_natify2";
Addsimps [mod_natify1, mod_natify2];

(** Quotient **)

Goal "natify(m) div n = m div n";
by (simp_tac (simpset() addsimps [div_def]) 1);
qed "div_natify1";

Goal "m div natify(n) = m div n";
by (simp_tac (simpset() addsimps [div_def]) 1);
qed "div_natify2";
Addsimps [div_natify1, div_natify2];


(*** Typing rules ***)

(** Addition **)

Goal "[| m:nat;  n:nat |] ==> raw_add (m, n) : nat";
by (induct_tac "m" 1);
by Auto_tac;
qed "raw_add_type";

Goal "m #+ n : nat";
by (simp_tac (simpset() addsimps [add_def, raw_add_type]) 1);
qed "add_type";
AddIffs [add_type];
AddTCs [add_type];

(** Multiplication **)

Goal "[| m:nat;  n:nat |] ==> raw_mult (m, n) : nat";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [raw_add_type])));
qed "raw_mult_type";

Goal "m #* n : nat";
by (simp_tac (simpset() addsimps [mult_def, raw_mult_type]) 1);
qed "mult_type";
AddIffs [mult_type];
AddTCs [mult_type];


(** Difference **)

Goal "[| m:nat;  n:nat |] ==> raw_diff (m, n) : nat";
by (induct_tac "n" 1);
by Auto_tac;
by (fast_tac (claset() addIs [nat_case_type]) 1);
qed "raw_diff_type";

Goal "m #- n : nat";
by (simp_tac (simpset() addsimps [diff_def, raw_diff_type]) 1);
qed "diff_type";
AddIffs [diff_type];
AddTCs [diff_type];

Goalw [diff_def] "0 #- n = 0";
by (rtac (natify_in_nat RS nat_induct) 1);
by Auto_tac;
qed "diff_0_eq_0";

(*Must simplify BEFORE the induction: else we get a critical pair*)
Goal "succ(m) #- succ(n) = m #- n";
by (simp_tac (simpset() addsimps [natify_succ, diff_def]) 1);
by (res_inst_tac [("x1","n")] (natify_in_nat RS nat_induct) 1);
by Auto_tac;
qed "diff_succ_succ";

(*This defining property is no longer wanted*)
Delsimps [raw_diff_succ];  

(*Natify has weakened this law, compared with the older approach*)
Goal "m #- 0 = natify(m)";
by (asm_simp_tac (simpset() addsimps [diff_def]) 1);
qed "diff_0";

Addsimps [diff_0, diff_0_eq_0, diff_succ_succ];

Goal "m:nat ==> (m #- n) le m";
by (subgoal_tac "(m #- natify(n)) le m" 1);
by (res_inst_tac [("m","m"), ("n","natify(n)")] diff_induct 2);
by (etac leE 6);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [le_iff])));
qed "diff_le_self";


(*** Addition ***)

(*Natify has weakened this law, compared with the older approach*)
Goal "0 #+ m = natify(m)";
by (asm_simp_tac (simpset() addsimps [add_def]) 1);
qed "add_0_natify";

Goal "succ(m) #+ n = succ(m #+ n)";
by (asm_simp_tac (simpset() addsimps [natify_succ, add_def]) 1);
qed "add_succ";

Addsimps [add_0_natify, add_succ];

Goal "m: nat ==> 0 #+ m = m";
by (Asm_simp_tac 1);
qed "add_0";

(*Associative law for addition*)
Goal "(m #+ n) #+ k = m #+ (n #+ k)";
by (subgoal_tac "(natify(m) #+ natify(n)) #+ natify(k) = \
\                natify(m) #+ (natify(n) #+ natify(k))" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by Auto_tac;
qed "add_assoc";

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
Goal "m #+ 0 = natify(m)";
by (subgoal_tac "natify(m) #+ 0 = natify(m)" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by Auto_tac;
qed "add_0_right_natify";

Goalw [add_def] "m #+ succ(n) = succ(m #+ n)";
by (res_inst_tac [("n","natify(m)")] nat_induct 1);
by (auto_tac (claset(), simpset() addsimps [natify_succ]));  
qed "add_succ_right";

Addsimps [add_0_right_natify, add_succ_right];

Goal "m: nat ==> m #+ 0 = m";
by Auto_tac;
qed "add_0_right";

(*Commutative law for addition*)  
Goal "m #+ n = n #+ m";
by (subgoal_tac "natify(m) #+ natify(n) = natify(n) #+ natify(m)" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by Auto_tac;
qed "add_commute";

(*for a/c rewriting*)
Goal "m#+(n#+k)=n#+(m#+k)";
by (rtac (add_commute RS trans) 1);
by (rtac (add_assoc RS trans) 1);
by (rtac (add_commute RS subst_context) 1);
qed "add_left_commute";

(*Addition is an AC-operator*)
bind_thms ("add_ac", [add_assoc, add_commute, add_left_commute]);

(*Cancellation law on the left*)
Goal "[| raw_add(k, m) = raw_add(k, n);  k:nat |] ==> m=n";
by (etac rev_mp 1);
by (induct_tac "k" 1);
by Auto_tac;
qed "raw_add_left_cancel";

Goalw [add_def] "k #+ m = k #+ n ==> natify(m) = natify(n)";
by (dtac raw_add_left_cancel 1);
by Auto_tac;
qed "add_left_cancel_natify";

Goal "[| i = j;  i #+ m = j #+ n;  m:nat;  n:nat |] ==> m = n";
by (force_tac (claset() addSDs [add_left_cancel_natify], simpset()) 1);
qed "add_left_cancel";

(*Thanks to Sten Agerholm*)
Goal "k#+m le k#+n ==> natify(m) le natify(n)";
by (res_inst_tac [("P", "natify(k)#+m le natify(k)#+n")] rev_mp 1);
by (res_inst_tac [("n","natify(k)")] nat_induct 2);
by Auto_tac;
qed "add_le_elim1_natify";

Goal "[| k#+m le k#+n; m: nat; n: nat |] ==> m le n";
by (dtac add_le_elim1_natify 1);
by Auto_tac;
qed "add_le_elim1";

Goal "k#+m < k#+n ==> natify(m) < natify(n)";
by (res_inst_tac [("P", "natify(k)#+m < natify(k)#+n")] rev_mp 1);
by (res_inst_tac [("n","natify(k)")] nat_induct 2);
by Auto_tac;
qed "add_lt_elim1_natify";

Goal "[| k#+m < k#+n; m: nat; n: nat |] ==> m < n";
by (dtac add_lt_elim1_natify 1);
by Auto_tac;
qed "add_lt_elim1";


(*** Monotonicity of Addition ***)

(*strict, in 1st argument; proof is by rule induction on 'less than'.
  Still need j:nat, for consider j = omega.  Then we can have i<omega,
  which is the same as i:nat, but natify(j)=0, so the conclusion fails.*)
Goal "[| i<j; j:nat |] ==> i#+k < j#+k";
by (ftac lt_nat_in_nat 1);
by (assume_tac 1);
by (etac succ_lt_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [leI])));
qed "add_lt_mono1";

(*strict, in both arguments*)
Goal "[| i<j; k<l; j:nat; l:nat |] ==> i#+k < j#+l";
by (rtac (add_lt_mono1 RS lt_trans) 1);
by (REPEAT (assume_tac 1));
by (EVERY [stac add_commute 1,
           stac add_commute 1,
           rtac add_lt_mono1 1]);
by (REPEAT (assume_tac 1));
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
Goal "[| i le j; j:nat |] ==> i#+k le j#+k";
by (res_inst_tac [("f", "%j. j#+k")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [add_lt_mono1, add_type RS nat_into_Ord] 1));
qed "add_le_mono1";

(* le monotonicity, BOTH arguments*)
Goal "[| i le j; k le l; j:nat; l:nat |] ==> i#+k le j#+l";
by (rtac (add_le_mono1 RS le_trans) 1);
by (REPEAT (assume_tac 1));
by (EVERY [stac add_commute 1,
           stac add_commute 1,
           rtac add_le_mono1 1]);
by (REPEAT (assume_tac 1));
qed "add_le_mono";

(** Subtraction is the inverse of addition. **)

Goal "(n#+m) #- n = natify(m)";
by (subgoal_tac "(natify(n) #+ m) #- natify(n) = natify(m)" 1);
by (res_inst_tac [("n","natify(n)")] nat_induct 2);
by Auto_tac;
qed "diff_add_inverse";

Goal "(m#+n) #- n = natify(m)";
by (simp_tac (simpset() addsimps [inst "m" "m" add_commute, 
				  diff_add_inverse]) 1);
qed "diff_add_inverse2";

Goal "(k#+m) #- (k#+n) = m #- n";
by (subgoal_tac "(natify(k) #+ natify(m)) #- (natify(k) #+ natify(n)) = \
\                natify(m) #- natify(n)" 1);
by (res_inst_tac [("n","natify(k)")] nat_induct 2);
by Auto_tac;
qed "diff_cancel";

Goal "(m#+k) #- (n#+k) = m #- n";
by (simp_tac (simpset() addsimps [inst "n" "k" add_commute, diff_cancel]) 1);
qed "diff_cancel2";

Goal "n #- (n#+m) = 0";
by (subgoal_tac "natify(n) #- (natify(n) #+ natify(m)) = 0" 1);
by (res_inst_tac [("n","natify(n)")] nat_induct 2);
by Auto_tac;
qed "diff_add_0";


(** Lemmas for the CancelNumerals simproc **)

Goal "(u #+ m = u #+ n) <-> (0 #+ m = natify(n))";
by Auto_tac;  
by (blast_tac (claset() addDs [add_left_cancel_natify]) 1);
by (asm_full_simp_tac (simpset() addsimps [add_def]) 1);
qed "eq_add_iff";

Goal "(u #+ m < u #+ n) <-> (0 #+ m < natify(n))";
by (auto_tac (claset(), simpset() addsimps [add_lt_elim1_natify]));
by (dtac add_lt_mono1 1);
by (auto_tac (claset(), simpset() addsimps [inst "m" "u" add_commute]));
qed "less_add_iff";

Goal "((u #+ m) #- (u #+ n)) = ((0 #+ m) #- n)";
by (asm_simp_tac (simpset() addsimps [diff_cancel]) 1);
qed "diff_add_eq";

(*To tidy up the result of a simproc.  Only the RHS will be simplified.*)
Goal "u = u' ==> (t==u) == (t==u')";
by Auto_tac;
qed "eq_cong2";

Goal "u <-> u' ==> (t==u) == (t==u')";
by Auto_tac;
qed "iff_cong2";


(*** Multiplication [the simprocs need these laws] ***)

Goal "0 #* m = 0";
by (simp_tac (simpset() addsimps [mult_def]) 1);
qed "mult_0";

Goal "succ(m) #* n = n #+ (m #* n)";
by (simp_tac (simpset() addsimps [add_def, mult_def, natify_succ, 
                                  raw_mult_type]) 1);
qed "mult_succ";

Addsimps [mult_0, mult_succ];

(*right annihilation in product*)
Goalw [mult_def] "m #* 0 = 0";
by (res_inst_tac [("n","natify(m)")] nat_induct 1);
by Auto_tac;
qed "mult_0_right";

(*right successor law for multiplication*)
Goal "m #* succ(n) = m #+ (m #* n)";
by (subgoal_tac "natify(m) #* succ(natify(n)) = \
\                natify(m) #+ (natify(m) #* natify(n))" 1);
by (full_simp_tac (simpset() addsimps [natify_succ, add_def, mult_def]) 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps add_ac)));
qed "mult_succ_right";

Addsimps [mult_0_right, mult_succ_right];

Goal "1 #* n = natify(n)";
by Auto_tac;
qed "mult_1_natify";

Goal "n #* 1 = natify(n)";
by Auto_tac;
qed "mult_1_right_natify";

Addsimps [mult_1_natify, mult_1_right_natify];

Goal "n : nat ==> 1 #* n = n";
by (Asm_simp_tac 1);
qed "mult_1";

Goal "n : nat ==> n #* 1 = n";
by (Asm_simp_tac 1);
qed "mult_1_right";

(*Commutative law for multiplication*)
Goal "m #* n = n #* m";
by (subgoal_tac "natify(m) #* natify(n) = natify(n) #* natify(m)" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by Auto_tac;
qed "mult_commute";

(*addition distributes over multiplication*)
Goal "(m #+ n) #* k = (m #* k) #+ (n #* k)";
by (subgoal_tac "(natify(m) #+ natify(n)) #* natify(k) = \
\                (natify(m) #* natify(k)) #+ (natify(n) #* natify(k))" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_assoc RS sym])));
qed "add_mult_distrib";

(*Distributive law on the left*)
Goal "k #* (m #+ n) = (k #* m) #+ (k #* n)";
by (subgoal_tac "natify(k) #* (natify(m) #+ natify(n)) = \
\                (natify(k) #* natify(m)) #+ (natify(k) #* natify(n))" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps add_ac)));
qed "add_mult_distrib_left";

(*Associative law for multiplication*)
Goal "(m #* n) #* k = m #* (n #* k)";
by (subgoal_tac "(natify(m) #* natify(n)) #* natify(k) = \
\                natify(m) #* (natify(n) #* natify(k))" 1);
by (res_inst_tac [("n","natify(m)")] nat_induct 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_mult_distrib])));
qed "mult_assoc";

(*for a/c rewriting*)
Goal "m #* (n #* k) = n #* (m #* k)";
by (rtac (mult_commute RS trans) 1);
by (rtac (mult_assoc RS trans) 1);
by (rtac (mult_commute RS subst_context) 1);
qed "mult_left_commute";

bind_thms ("mult_ac", [mult_assoc,mult_commute,mult_left_commute]);
