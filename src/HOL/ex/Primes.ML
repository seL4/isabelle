(*  Title:      HOL/ex/Primes.ML
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm

See H. Davenport, "The Higher Arithmetic".  6th edition.  (CUP, 1992)
*)

eta_contract:=false;

open Primes;

(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(*** Euclid's Algorithm ***)


(** Prove the termination condition and remove it from the recursion equations
    and induction rule **)

Tfl.tgoalw thy [] gcd.rules;
by (simp_tac (!simpset addsimps [mod_less_divisor, zero_less_eq]) 1);
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

(*gcd(m,n) divides m and n.  The conjunctions don't seem provable separately*)
goal thy "(gcd(m,n) dvd m) & (gcd(m,n) dvd n)";
by (res_inst_tac [("u","m"),("v","n")] gcd_induct 1);
by (case_tac "n=0" 1);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [mod_less_divisor,zero_less_eq])));
by (blast_tac (!claset addDs [dvd_mod_imp_dvd]) 1);
qed "gcd_divides_both";

(*Maximality: for all m,n,f naturals, 
                if f divides m and f divides n then f divides gcd(m,n)*)
goal thy "!!k. (f dvd m) --> (f dvd n) --> f dvd gcd(m,n)";
by (res_inst_tac [("u","m"),("v","n")] gcd_induct 1);
by (case_tac "n=0" 1);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [dvd_mod, mod_less_divisor,
				      zero_less_eq])));
qed_spec_mp "gcd_greatest";

(*Function gcd yields the Greatest Common Divisor*)
goalw thy [is_gcd_def] "is_gcd (gcd(m,n)) m n";
by (asm_simp_tac (!simpset addsimps [gcd_greatest, gcd_divides_both]) 1);
qed "is_gcd";

(*uniqueness of GCDs*)
goalw thy [is_gcd_def] "is_gcd m a b & is_gcd n a b --> m=n";
by (blast_tac (!claset addIs [dvd_anti_sym]) 1);
qed "is_gcd_unique";

(*Davenport, page 27*)
goal thy "k * gcd(m,n) = gcd(k*m, k*n)";
by (res_inst_tac [("u","m"),("v","n")] gcd_induct 1);
by (case_tac "k=0" 1);
by (case_tac "n=0" 2);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [mod_less_divisor, zero_less_eq,
				      mod_geq, mod_mult_distrib2])));
qed "gcd_mult_distrib2";

(*This theorem leads immediately to a proof of the uniqueness of factorization.
  If p divides a product of primes then it is one of those primes.*)
goalw thy [prime_def] "!!p. [| p: prime; p dvd (m*n) |] ==> p dvd m | p dvd n";
by (Step_tac 1);
by (subgoal_tac "m = gcd(m*p, m*n)" 1);
by (etac ssubst 1);
by (rtac gcd_greatest 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [gcd_mult_distrib2 RS sym])));
(*Now deduce  gcd(p,n)=1  to finish the proof*)
by (cut_inst_tac [("m","p"),("n","n")] gcd_divides_both 1);
by (fast_tac (!claset addSss (!simpset)) 1);
qed "prime_dvd_mult";
