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

(* GCD by Euclid's Algorithm *)

val [rew] = goal HOL.thy "x==y ==> x=y";
by (rewtac rew);
by (rtac refl 1);
qed "equals_reflection";

goal thy "(%n m. egcd m n) = wfrec (pred_nat^+)   \
\                                  (%f n m. if n=0 then m else f (m mod n) n)";
by (simp_tac (HOL_ss addsimps [egcd_def]) 1);
val egcd_def1 = result() RS eq_reflection;

goalw thy [egcd_def] "egcd m 0 = m";
by (simp_tac (!simpset addsimps [wf_pred_nat RS wf_trancl RS wfrec]) 1);
qed "egcd_0";

goal thy "!!m. 0<n ==> egcd m n = egcd n (m mod n)";
by (rtac (egcd_def1 RS wf_less_trans RS fun_cong) 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor, cut_apply, less_eq]) 1);
qed "egcd_less_0";
Addsimps [egcd_0, egcd_less_0];

goal thy "(egcd m 0) dvd m";
by (Simp_tac 1);
qed "egcd_0_dvd_m";

goal thy "(egcd m 0) dvd 0";
by (Simp_tac 1);
qed "egcd_0_dvd_0";

goalw thy [dvd_def] "!!k. [| k dvd m; k dvd n |] ==> k dvd (m + n)";
by (fast_tac (!claset addIs [add_mult_distrib2 RS sym]) 1);
qed "dvd_add";

goalw thy [dvd_def] "!!k. k dvd m ==> k dvd (q * m)";
by (fast_tac (!claset addIs [mult_left_commute]) 1);
qed "dvd_mult";

goal thy "!!k. [| k dvd n; k dvd (m mod n); 0 < n |] ==> k dvd m";
by (deepen_tac 
    (!claset addIs [mod_div_equality RS subst]
             addSIs [dvd_add, dvd_mult]) 0 1);
qed "gcd_ind";


(* Property 1: egcd m n divides m and n *)

goal thy "ALL m. (egcd m n dvd m) & (egcd m n dvd n)";
by (res_inst_tac [("n","n")] less_induct 1);
by (rtac allI 1);
by (case_tac "n=0" 1);
(* case n = 0 *)
by (Asm_simp_tac 1);
(* case n > 0 *)
by (asm_full_simp_tac (!simpset addsimps [zero_less_eq RS sym]) 1);
by (eres_inst_tac [("x","m mod n")] allE 1);
by (asm_full_simp_tac (!simpset addsimps [mod_less_divisor]) 1);
by (fast_tac (!claset addIs [gcd_ind]) 1);
qed "egcd_prop1";


(* if f divides m and n then f divides egcd m n *)

Delsimps [add_mult_distrib,add_mult_distrib2];


goalw thy [dvd_def] "!!m. [| f dvd m; f dvd n; 0<n |] ==> f dvd (m mod n)";
by (Step_tac 1);
by (rtac (zero_less_mult_iff RS iffD1 RS conjE) 1);
by (REPEAT_SOME assume_tac);
by (res_inst_tac 
    [("x", "(((k div ka)*ka + k mod ka) - ((f*k) div (f*ka)) * ka)")] 
    exI 1);
by (asm_simp_tac (!simpset addsimps [diff_mult_distrib2, div_cancel,
                                     mult_mod_distrib, add_mult_distrib2,
                                     diff_add_inverse]) 1);
qed "dvd_mod";


(* Property 2: for all m,n,f naturals, 
               if f divides m and f divides n then f divides egcd m n*)
goal thy "!!k. ALL m. (f dvd m) & (f dvd k) --> f dvd egcd m k";
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac allI 1);
by (case_tac "n=0" 1);
(* case n = 0 *)
by (Asm_simp_tac 1);
(* case n > 0 *)
by (Step_tac 1);
by (asm_full_simp_tac (!simpset addsimps [zero_less_eq RS sym]) 1);
by (eres_inst_tac [("x","m mod n")] allE 1);
by (asm_full_simp_tac (!simpset addsimps [mod_less_divisor]) 1);
by (fast_tac (!claset addSIs [dvd_mod]) 1);
qed "egcd_prop2";

(* GCD PROOF : GCD exists and egcd fits the definition *)

goalw thy [gcd_def] "gcd (egcd m n) m n";
by (asm_simp_tac (!simpset addsimps [egcd_prop1]) 1);
by (fast_tac (!claset addIs [egcd_prop2 RS spec RS mp]) 1);
qed "gcd";

(* GCD is unique *)

goalw thy [gcd_def] "gcd m a b & gcd n a b --> m=n";
by (fast_tac (!claset addIs [dvd_anti_sym]) 1);
qed "gcd_unique";

