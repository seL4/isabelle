(*  Title: 	ZF/arith.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
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
val rec_0 = result();

goal Arith.thy "rec(succ(m),a,b) = b(m, rec(m,a,b))";
by (rtac rec_trans 1);
by (simp_tac (ZF_ss addsimps [nat_case_succ, nat_succI]) 1);
val rec_succ = result();

val major::prems = goal Arith.thy
    "[| n: nat;  \
\       a: C(0);  \
\       !!m z. [| m: nat;  z: C(m) |] ==> b(m,z): C(succ(m))  \
\    |] ==> rec(n,a,b) : C(n)";
by (rtac (major RS nat_induct) 1);
by (ALLGOALS
    (asm_simp_tac (ZF_ss addsimps (prems@[rec_0,rec_succ]))));
val rec_type = result();

val nat_typechecks = [rec_type,nat_0I,nat_1I,nat_succI,Ord_nat];

val nat_ss = ZF_ss addsimps ([rec_0,rec_succ] @ nat_typechecks);


(** Addition **)

val add_type = prove_goalw Arith.thy [add_def]
    "[| m:nat;  n:nat |] ==> m #+ n : nat"
 (fn prems=> [ (typechk_tac (prems@nat_typechecks@ZF_typechecks)) ]);

val add_0 = prove_goalw Arith.thy [add_def]
    "0 #+ n = n"
 (fn _ => [ (rtac rec_0 1) ]);

val add_succ = prove_goalw Arith.thy [add_def]
    "succ(m) #+ n = succ(m #+ n)"
 (fn _=> [ (rtac rec_succ 1) ]); 

(** Multiplication **)

val mult_type = prove_goalw Arith.thy [mult_def]
    "[| m:nat;  n:nat |] ==> m #* n : nat"
 (fn prems=>
  [ (typechk_tac (prems@[add_type]@nat_typechecks@ZF_typechecks)) ]);

val mult_0 = prove_goalw Arith.thy [mult_def]
    "0 #* n = 0"
 (fn _ => [ (rtac rec_0 1) ]);

val mult_succ = prove_goalw Arith.thy [mult_def]
    "succ(m) #* n = n #+ (m #* n)"
 (fn _ => [ (rtac rec_succ 1) ]); 

(** Difference **)

val diff_type = prove_goalw Arith.thy [diff_def]
    "[| m:nat;  n:nat |] ==> m #- n : nat"
 (fn prems=> [ (typechk_tac (prems@nat_typechecks@ZF_typechecks)) ]);

val diff_0 = prove_goalw Arith.thy [diff_def]
    "m #- 0 = m"
 (fn _ => [ (rtac rec_0 1) ]);

val diff_0_eq_0 = prove_goalw Arith.thy [diff_def]
    "n:nat ==> 0 #- n = 0"
 (fn [prem]=>
  [ (rtac (prem RS nat_induct) 1),
    (ALLGOALS (asm_simp_tac nat_ss)) ]);

(*Must simplify BEFORE the induction!!  (Else we get a critical pair)
  succ(m) #- succ(n)   rewrites to   pred(succ(m) #- n)  *)
val diff_succ_succ = prove_goalw Arith.thy [diff_def]
    "[| m:nat;  n:nat |] ==> succ(m) #- succ(n) = m #- n"
 (fn prems=>
  [ (asm_simp_tac (nat_ss addsimps prems) 1),
    (nat_ind_tac "n" prems 1),
    (ALLGOALS (asm_simp_tac (nat_ss addsimps prems))) ]);

(*The conclusion is equivalent to m#-n <= m *)
val prems = goal Arith.thy 
    "[| m:nat;  n:nat |] ==> m #- n : succ(m)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
by (etac succE 3);
by (ALLGOALS
    (asm_simp_tac
     (nat_ss addsimps (prems @ [succ_iff, diff_0, diff_0_eq_0, 
				diff_succ_succ]))));
val diff_less_succ = result();

(*** Simplification over add, mult, diff ***)

val arith_typechecks = [add_type, mult_type, diff_type];
val arith_rews = [add_0, add_succ,
		  mult_0, mult_succ,
		  diff_0, diff_0_eq_0, diff_succ_succ];

val arith_ss = nat_ss addsimps (arith_rews@arith_typechecks);

(*** Addition ***)

(*Associative law for addition*)
val add_assoc = prove_goal Arith.thy 
    "m:nat ==> (m #+ n) #+ k = m #+ (n #+ k)"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]);

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
val add_0_right = prove_goal Arith.thy
    "m:nat ==> m #+ 0 = m"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]); 

val add_succ_right = prove_goal Arith.thy
    "m:nat ==> m #+ succ(n) = succ(m #+ n)"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]); 

(*Commutative law for addition*)  
val add_commute = prove_goal Arith.thy 
    "[| m:nat;  n:nat |] ==> m #+ n = n #+ m"
 (fn prems=>
  [ (nat_ind_tac "n" prems 1),
    (ALLGOALS
     (asm_simp_tac
      (arith_ss addsimps (prems@[add_0_right, add_succ_right])))) ]);

(*Cancellation law on the left*)
val [knat,eqn] = goal Arith.thy 
    "[| k:nat;  k #+ m = k #+ n |] ==> m=n";
by (rtac (eqn RS rev_mp) 1);
by (nat_ind_tac "k" [knat] 1);
by (ALLGOALS (simp_tac arith_ss));
by (fast_tac ZF_cs 1);
val add_left_cancel = result();

(*** Multiplication ***)

(*right annihilation in product*)
val mult_0_right = prove_goal Arith.thy 
    "m:nat ==> m #* 0 = 0"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems)))  ]);

(*right successor law for multiplication*)
val mult_succ_right = prove_goal Arith.thy 
    "!!m n. [| m:nat;  n:nat |] ==> m #* succ(n) = m #+ (m #* n)"
 (fn _=>
  [ (nat_ind_tac "m" [] 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps [add_assoc RS sym]))),
       (*The final goal requires the commutative law for addition*)
    (rtac (add_commute RS subst_context) 1),
    (REPEAT (assume_tac 1))  ]);

(*Commutative law for multiplication*)
val mult_commute = prove_goal Arith.thy 
    "[| m:nat;  n:nat |] ==> m #* n = n #* m"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac
	     (arith_ss addsimps (prems@[mult_0_right, mult_succ_right])))) ]);

(*addition distributes over multiplication*)
val add_mult_distrib = prove_goal Arith.thy 
    "!!m n. [| m:nat;  k:nat |] ==> (m #+ n) #* k = (m #* k) #+ (n #* k)"
 (fn _=>
  [ (etac nat_induct 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps [add_assoc RS sym]))) ]);

(*Distributive law on the left; requires an extra typing premise*)
val add_mult_distrib_left = prove_goal Arith.thy 
    "[| m:nat;  n:nat;  k:nat |] ==> k #* (m #+ n) = (k #* m) #+ (k #* n)"
 (fn prems=>
      let val mult_commute' = read_instantiate [("m","k")] mult_commute
          val ss = arith_ss addsimps ([mult_commute',add_mult_distrib]@prems)
      in [ (simp_tac ss 1) ]
      end);

(*Associative law for multiplication*)
val mult_assoc = prove_goal Arith.thy 
    "!!m n k. [| m:nat;  n:nat;  k:nat |] ==> (m #* n) #* k = m #* (n #* k)"
 (fn _=>
  [ (etac nat_induct 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps [add_mult_distrib]))) ]);


(*** Difference ***)

val diff_self_eq_0 = prove_goal Arith.thy 
    "m:nat ==> m #- m = 0"
 (fn prems=>
  [ (nat_ind_tac "m" prems 1),
    (ALLGOALS (asm_simp_tac (arith_ss addsimps prems))) ]);

(*Addition is the inverse of subtraction: if n<=m then n+(m-n) = m. *)
val notless::prems = goal Arith.thy
    "[| ~m:n;  m:nat;  n:nat |] ==> n #+ (m#-n) = m";
by (rtac (notless RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
by (ALLGOALS (asm_simp_tac
	      (arith_ss addsimps (prems@[succ_mem_succ_iff, nat_0_in_succ,
					 naturals_are_ordinals]))));
val add_diff_inverse = result();


(*Subtraction is the inverse of addition. *)
val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> (n#+m) #-n = m";
by (rtac (nnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [mnat])));
val diff_add_inverse = result();

val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> n #- (n#+m) = 0";
by (rtac (nnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [mnat])));
val diff_add_0 = result();


(*** Remainder ***)

(*In ordinary notation: if 0<n and n<=m then m-n < m *)
goal Arith.thy "!!m n. [| 0:n; ~ m:n;  m:nat;  n:nat |] ==> m #- n : m";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (nat_ss addsimps [diff_less_succ,diff_succ_succ])));
val div_termination = result();

val div_rls =
    [Ord_transrec_type, apply_type, div_termination, if_type] @ 
    nat_typechecks;

(*Type checking depends upon termination!*)
val prems = goalw Arith.thy [mod_def]
    "[| 0:n;  m:nat;  n:nat |] ==> m mod n : nat";
by (REPEAT (ares_tac (prems @ div_rls) 1 ORELSE etac Ord_trans 1));
val mod_type = result();

val div_ss = ZF_ss addsimps [naturals_are_ordinals,div_termination];

val prems = goal Arith.thy "[| 0:n;  m:n;  m:nat;  n:nat |] ==> m mod n = m";
by (rtac (mod_def RS def_transrec RS trans) 1);
by (simp_tac (div_ss addsimps prems) 1);
val mod_less = result();

val prems = goal Arith.thy
    "[| 0:n;  ~m:n;  m:nat;  n:nat |] ==> m mod n = (m#-n) mod n";
by (rtac (mod_def RS def_transrec RS trans) 1);
by (simp_tac (div_ss addsimps prems) 1);
val mod_geq = result();

(*** Quotient ***)

(*Type checking depends upon termination!*)
val prems = goalw Arith.thy [div_def]
    "[| 0:n;  m:nat;  n:nat |] ==> m div n : nat";
by (REPEAT (ares_tac (prems @ div_rls) 1 ORELSE etac Ord_trans 1));
val div_type = result();

val prems = goal Arith.thy
    "[| 0:n;  m:n;  m:nat;  n:nat |] ==> m div n = 0";
by (rtac (div_def RS def_transrec RS trans) 1);
by (simp_tac (div_ss addsimps prems) 1);
val div_less = result();

val prems = goal Arith.thy
    "[| 0:n;  ~m:n;  m:nat;  n:nat |] ==> m div n = succ((m#-n) div n)";
by (rtac (div_def RS def_transrec RS trans) 1);
by (simp_tac (div_ss addsimps prems) 1);
val div_geq = result();

(*Main Result.*)
val prems = goal Arith.thy
    "[| 0:n;  m:nat;  n:nat |] ==> (m div n)#*n #+ m mod n = m";
by (res_inst_tac [("i","m")] complete_induct 1);
by (resolve_tac prems 1);
by (res_inst_tac [("Q","x:n")] (excluded_middle RS disjE) 1);
by (ALLGOALS 
    (asm_simp_tac
     (arith_ss addsimps ([mod_type,div_type] @ prems @
        [mod_less,mod_geq, div_less, div_geq,
	 add_assoc, add_diff_inverse, div_termination]))));
val mod_div_equality = result();


(**** Additional theorems about "less than" ****)

val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> ~ (m #+ n) : n";
by (rtac (mnat RS nat_induct) 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [mem_not_refl])));
by (rtac notI 1);
by (etac notE 1);
by (etac (succI1 RS Ord_trans) 1);
by (rtac (nnat RS naturals_are_ordinals) 1);
val add_not_less_self = result();

val [mnat,nnat] = goal Arith.thy
    "[| m:nat;  n:nat |] ==> m : succ(m #+ n)";
by (rtac (mnat RS nat_induct) 1);
(*May not simplify even with ZF_ss because it would expand m:succ(...) *)
by (rtac (add_0 RS ssubst) 1);
by (rtac (add_succ RS ssubst) 2);
by (REPEAT (ares_tac [nnat, nat_0_in_succ, succ_mem_succI, 
		      naturals_are_ordinals, nat_succI, add_type] 1));
val add_less_succ_self = result();

goal Arith.thy "!!m n. [| m:nat;  n:nat |] ==> m <= m #+ n";
by (rtac (add_less_succ_self RS member_succD) 1);
by (REPEAT (ares_tac [naturals_are_ordinals, add_type] 1));
val add_leq_self = result();

goal Arith.thy "!!m n. [| m:nat;  n:nat |] ==> m <= n #+ m";
by (rtac (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [add_leq_self] 1));
val add_leq_self2 = result();

(** Monotonicity of addition **)

(*strict, in 1st argument*)
goal Arith.thy "!!i j k. [| i:j; j:nat |] ==> i#+k : j#+k";
by (etac succ_less_induct 1);
by (ALLGOALS (asm_simp_tac (arith_ss addsimps [succ_iff])));
val add_less_mono1 = result();

(*strict, in both arguments*)
goal Arith.thy "!!i j k l. [| i:j; k:l; j:nat; l:nat |] ==> i#+k : j#+l";
by (rtac (add_less_mono1 RS Ord_trans) 1);
by (REPEAT_FIRST (ares_tac [add_type, naturals_are_ordinals]));
by (EVERY [rtac (add_commute RS ssubst) 1,
	   rtac (add_commute RS ssubst) 3,
	   rtac add_less_mono1 5]);
by (REPEAT (ares_tac [Ord_nat RSN (3,Ord_trans)] 1));
val add_less_mono = result();

(*A [clumsy] way of lifting < monotonictity to <= monotonicity *)
val less_mono::ford::prems = goal Ord.thy
     "[| !!i j. [| i:j; j:k |] ==> f(i) : f(j);	\
\        !!i. i:k ==> f(i):k;			\
\        i<=j;  i:k;  j:k;  Ord(k)		\
\     |] ==> f(i) <= f(j)";
by (cut_facts_tac prems 1);
by (rtac member_succD 1);
by (dtac member_succI 1);
by (fast_tac (ZF_cs addSIs [less_mono]) 3);
by (REPEAT (ares_tac [ford,Ord_in_Ord] 1));
val Ord_less_mono_imp_mono = result();

(*<=, in 1st argument*)
goal Arith.thy
    "!!i j k. [| i<=j; i:nat; j:nat; k:nat |] ==> i#+k <= j#+k";
by (res_inst_tac [("f", "%j.j#+k")] Ord_less_mono_imp_mono 1);
by (REPEAT (ares_tac [add_less_mono1, add_type, Ord_nat] 1));
val add_mono1 = result();

(*<=, in both arguments*)
goal Arith.thy
    "!!i j k. [| i<=j; k<=l; i:nat; j:nat; k:nat; l:nat |] ==> i#+k <= j#+l";
by (rtac (add_mono1 RS subset_trans) 1);
by (REPEAT (assume_tac 1));
by (EVERY [rtac (add_commute RS ssubst) 1,
	   rtac (add_commute RS ssubst) 3,
	   rtac add_mono1 5]);
by (REPEAT (assume_tac 1));
val add_mono = result();
