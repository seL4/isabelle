(*  Title:      HOL/ex/Primes.ML
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

goalw thy [dvd_def] "m dvd 0";
by (fast_tac (!claset addIs [mult_0_right RS sym]) 1);
qed "dvd_0_right";
Addsimps [dvd_0_right];

goalw thy [dvd_def] "!!m. 0 dvd m ==> m = 0";
by (fast_tac (!claset addss !simpset) 1);
qed "dvd_0_left";

goalw thy [dvd_def] "m dvd m";
by (fast_tac (!claset addIs [mult_1_right RS sym]) 1);
qed "dvd_refl";
Addsimps [dvd_refl];

goalw thy [dvd_def] "!!m n p. [| m dvd n; n dvd p |] ==> m dvd p";
by (fast_tac (!claset addIs [mult_assoc] ) 1);
qed "dvd_trans";

goalw thy [dvd_def] "!!m n. [| m dvd n; n dvd m |] ==> m=n";
by (fast_tac (!claset addDs [mult_eq_self_implies_10]
                     addss (!simpset addsimps [mult_assoc, mult_eq_1_iff])) 1);
qed "dvd_anti_sym";


(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(* Euclid's Algorithm *)


Tfl.tgoalw thy [] gcd.rules;
by (simp_tac (!simpset addsimps [mod_less_divisor,zero_less_eq]) 1);
val tc = result();

val gcd_eq = tc RS hd gcd.rules;
val gcd_induct = tc RS gcd.induct;

goal thy "gcd(m,0) = m";
by (rtac (gcd_eq RS trans) 1);
by (Simp_tac 1);
qed "gcd_0";

goal thy "!!m. 0<n ==> gcd(m,n) = gcd (n, m mod n)";
by (rtac (gcd_eq RS trans) 1);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
qed "gcd_less_0";
Addsimps [gcd_0, gcd_less_0];

goal thy "gcd(m,0) dvd m";
by (Simp_tac 1);
qed "gcd_0_dvd_m";

goal thy "gcd(m,0) dvd 0";
by (Simp_tac 1);
qed "gcd_0_dvd_0";

goalw thy [dvd_def] "!!k. [| k dvd m; k dvd n |] ==> k dvd (m + n)";
by (blast_tac (!claset addIs [add_mult_distrib2 RS sym]) 1);
qed "dvd_add";

goalw thy [dvd_def] "!!k. k dvd m ==> k dvd (q * m)";
by (blast_tac (!claset addIs [mult_left_commute]) 1);
qed "dvd_mult";

goal thy "!!k. [| k dvd (m mod n); k dvd n; n~=0 |] ==> k dvd m";
by (subgoal_tac "k dvd ((m div n)*n + m mod n)" 1);
by (asm_simp_tac (!simpset addsimps [dvd_add, dvd_mult]) 2);
by (asm_full_simp_tac (!simpset addsimps [mod_div_equality, zero_less_eq]) 1);
qed "gcd_recursion";


(*gcd(m,n) divides m and n.  The conjunctions don't seem provable separately*)
goal thy "(gcd(m,n) dvd m) & (gcd(m,n) dvd n)";
by (res_inst_tac [("v","m"),("v1.0","n")] gcd_induct 1);
by (case_tac "n=0" 1);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [mod_less_divisor,zero_less_eq])));
by (blast_tac (!claset addDs [gcd_recursion]) 1);
qed "gcd_divides_both";


(* if f divides m and n then f divides gcd(m,n) *)

goalw thy [dvd_def] "!!m. [| f dvd m; f dvd n; 0<n |] ==> f dvd (m mod n)";
by (Step_tac 1);
by (full_simp_tac (!simpset addsimps [zero_less_mult_iff]) 1);
by (res_inst_tac 
    [("x", "(((k div ka)*ka + k mod ka) - ((f*k) div (f*ka)) * ka)")] 
    exI 1);
by (asm_simp_tac (!simpset addsimps [diff_mult_distrib2, 
                                     mult_mod_distrib, add_mult_distrib2]) 1);
qed "dvd_mod";


(*Maximality: for all m,n,f naturals, 
                if f divides m and f divides n then f divides gcd(m,n)*)
goal thy "!!k. (f dvd m) & (f dvd n) --> f dvd gcd(m,n)";
by (res_inst_tac [("v","m"),("v1.0","n")] gcd_induct 1);
by (case_tac "n=0" 1);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [dvd_mod, mod_less_divisor,
				      zero_less_eq])));
qed_spec_mp "gcd_greatest";

(* GCD PROOF : GCD exists and gcd fits the definition *)

goalw thy [is_gcd_def] "is_gcd (gcd(m,n)) m n";
by (asm_simp_tac (!simpset addsimps [gcd_greatest, gcd_divides_both]) 1);
qed "is_gcd";

(* GCD is unique *)

goalw thy [is_gcd_def] "is_gcd m a b & is_gcd n a b --> m=n";
by (blast_tac (!claset addIs [dvd_anti_sym]) 1);
qed "is_gcd_unique";

