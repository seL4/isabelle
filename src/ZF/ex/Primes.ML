(*  Title:      ZF/ex/Primes.ML
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm
*)

eta_contract:=false;

open Primes;

(************************************************)
(** Divides Relation                           **)
(************************************************)

goalw thy [dvd_def] "!!m. m dvd n ==> m:nat & n:nat & (EX k:nat. n = m#*k)";
by (assume_tac 1);
qed "dvdD";

bind_thm ("dvd_imp_nat1", dvdD RS conjunct1);
bind_thm ("dvd_imp_nat2", dvdD RS conjunct2 RS conjunct1);


goalw thy [dvd_def] "!!m. m:nat ==> m dvd 0";
by (fast_tac (claset() addIs [nat_0I, mult_0_right RS sym]) 1);
qed "dvd_0_right";

goalw thy [dvd_def] "!!m. 0 dvd m ==> m = 0";
by (fast_tac (claset() addss (simpset())) 1);
qed "dvd_0_left";

goalw thy [dvd_def] "!!m. m:nat ==> m dvd m";
by (fast_tac (claset() addIs [nat_1I, mult_1_right RS sym]) 1);
qed "dvd_refl";

goalw thy [dvd_def] "!!m n p. [| m dvd n; n dvd p |] ==> m dvd p";
by (fast_tac (claset() addIs [mult_assoc, mult_type] ) 1);
qed "dvd_trans";

goalw thy [dvd_def] "!!m n. [| m dvd n; n dvd m |] ==> m=n";
by (fast_tac (claset() addDs [mult_eq_self_implies_10]
                    addss (simpset() addsimps [mult_assoc, mult_eq_1_iff])) 1);
qed "dvd_anti_sym";


(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(* GCD by Euclid's Algorithm *)

goalw thy [egcd_def] "!!m. m:nat ==> egcd(m,0) = m";
by (stac transrec 1);
by (Asm_simp_tac 1);
qed "egcd_0";

goalw thy [egcd_def]
    "!!m. [| 0<n; m:nat; n:nat |] ==> egcd(m,n) = egcd(n, m mod n)";
by (res_inst_tac [("P", "%z. ?left(z) = ?right")] (transrec RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [ltD RS mem_imp_not_eq RS not_sym,
                                     mod_less_divisor RS ltD]) 1);
qed "egcd_lt_0";

goal thy "!!m. m:nat ==> egcd(m,0) dvd m";
by (asm_simp_tac (simpset() addsimps [egcd_0,dvd_refl]) 1);
qed "egcd_0_dvd_m";

goal thy "!!m. m:nat ==> egcd(m,0) dvd 0";
by (asm_simp_tac (simpset() addsimps [egcd_0,dvd_0_right]) 1);
qed "egcd_0_dvd_0";

goalw thy [dvd_def] "!!k. [| k dvd a; k dvd b |] ==> k dvd (a #+ b)";
by (fast_tac (claset() addIs [add_mult_distrib_left RS sym, add_type]) 1);
qed "dvd_add";

goalw thy [dvd_def] "!!k. [| k dvd a; q:nat |] ==> k dvd (q #* a)";
by (fast_tac (claset() addIs [mult_left_commute, mult_type]) 1);
qed "dvd_mult";

goal thy "!!k. [| k dvd b; k dvd (a mod b); 0 < b; a:nat |] ==> k dvd a";
by (deepen_tac 
    (claset() addIs [mod_div_equality RS subst]
           addDs [dvdD]
           addSIs [dvd_add, dvd_mult, mult_type,mod_type,div_type]) 0 1);
qed "gcd_ind";


(* egcd type *)

goal thy "!!b. b:nat ==> ALL a:nat. egcd(a,b):nat";
by (etac complete_induct 1);
by (rtac ballI 1);
by (excluded_middle_tac "x=0" 1);
(* case x = 0 *)
by (asm_simp_tac (simpset() addsimps [egcd_0]) 2);
(* case x > 0 *)
by (asm_simp_tac (simpset() addsimps [egcd_lt_0, nat_into_Ord RS Ord_0_lt]) 1);
by (eres_inst_tac [("x","a mod x")] ballE 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [mod_less_divisor RS ltD, 
                                          nat_into_Ord RS Ord_0_lt]) 1);
qed "egcd_type";


(* Property 1: egcd(a,b) divides a and b *)

goal thy "!!b. b:nat ==> ALL a: nat. (egcd(a,b) dvd a) & (egcd(a,b) dvd b)";
by (res_inst_tac [("i","b")] complete_induct 1);
by (assume_tac 1);
by (rtac ballI 1);
by (excluded_middle_tac "x=0" 1);
(* case x = 0 *)
by (asm_simp_tac (simpset() addsimps [egcd_0,dvd_refl,dvd_0_right]) 2);
(* case x > 0 *)
by (asm_simp_tac (simpset() addsimps [egcd_lt_0, nat_into_Ord RS Ord_0_lt]) 1);
by (eres_inst_tac [("x","a mod x")] ballE 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [mod_less_divisor RS ltD, 
                                          nat_into_Ord RS Ord_0_lt]) 2);
by (best_tac (claset() addIs [gcd_ind, nat_into_Ord RS Ord_0_lt]) 1);
qed "egcd_prop1";


(* if f divides a and b then f divides egcd(a,b) *)

goalw thy [dvd_def] "!!a. [| f dvd a; f dvd b; 0<b |] ==> f dvd (a mod b)";
by (safe_tac (claset() addSIs [mult_type, mod_type]));
ren "m n" 1;
by (rtac (zero_lt_mult_iff RS iffD1 RS conjE) 1);
by (REPEAT_SOME assume_tac);
by (res_inst_tac 
    [("x", "(((m div n)#*n #+ m mod n) #- ((f#*m) div (f#*n)) #* n)")] 
    bexI 1);
by (asm_simp_tac (simpset() addsimps [diff_mult_distrib2, div_cancel,
                                     mult_mod_distrib, add_mult_distrib_left,
                                     diff_add_inverse]) 1);
by (Asm_simp_tac 1);
qed "dvd_mod";


(* Property 2: for all a,b,f naturals, 
               if f divides a and f divides b then f divides egcd(a,b)*)
goal thy "!!b. [| b:nat; f:nat |] ==>    \
\              ALL a. (f dvd a) & (f dvd b) --> f dvd egcd(a,b)";
by (etac complete_induct 1);
by (rtac allI 1);
by (excluded_middle_tac "x=0" 1);
(* case x = 0 *)
by (asm_simp_tac (simpset() addsimps [egcd_0,dvd_refl,dvd_0_right,
                                     dvd_imp_nat2]) 2);
(* case x > 0 *)
by (safe_tac (claset()));
by (asm_simp_tac (simpset() addsimps [egcd_lt_0, nat_into_Ord RS Ord_0_lt,
                                     dvd_imp_nat2]) 1);
by (eres_inst_tac [("x","a mod x")] ballE 1);
by (asm_full_simp_tac 
    (simpset() addsimps [mod_less_divisor RS ltD, dvd_imp_nat2, 
                        nat_into_Ord RS Ord_0_lt, egcd_lt_0]) 2);
by (fast_tac (claset() addSIs [dvd_mod, nat_into_Ord RS Ord_0_lt]) 1);
qed "egcd_prop2";

(* GCD PROOF : GCD exists and egcd fits the definition *)

goalw thy [gcd_def] "!!b. [| a: nat; b:nat |] ==> gcd(egcd(a,b), a, b)";
by (asm_simp_tac (simpset() addsimps [egcd_prop1]) 1);
by (fast_tac (claset() addIs [egcd_prop2 RS spec RS mp, dvd_imp_nat1]) 1);
qed "gcd";

(* GCD is unique *)

goalw thy [gcd_def] "!!a. gcd(m,a,b) & gcd(n,a,b) --> m=n";
by (fast_tac (claset() addIs [dvd_anti_sym]) 1);
qed "gcd_unique";

