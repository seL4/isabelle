(*  Title:      ZF/ex/Primes.ML
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm
*)

(************************************************)
(** Divides Relation                           **)
(************************************************)

Goalw [dvd_def] "m dvd n ==> m \\<in> nat & n \\<in> nat & (\\<exists>k \\<in> nat. n = m#*k)";
by (assume_tac 1);
qed "dvdD";

Goal "!!P. [|m dvd n;  !!k. [|m \\<in> nat; n \\<in> nat; k \\<in> nat; n = m#*k|] ==> P|] \
\          ==> P";
by (blast_tac (claset() addSDs [dvdD]) 1); 
qed "dvdE";

bind_thm ("dvd_imp_nat1", dvdD RS conjunct1);
bind_thm ("dvd_imp_nat2", dvdD RS conjunct2 RS conjunct1);


Goalw [dvd_def] "m \\<in> nat ==> m dvd 0";
by (fast_tac (claset() addIs [nat_0I, mult_0_right RS sym]) 1);
qed "dvd_0_right";
Addsimps [dvd_0_right];

Goalw [dvd_def] "0 dvd m ==> m = 0";
by (fast_tac (claset() addss (simpset())) 1);
qed "dvd_0_left";

Goalw [dvd_def] "m \\<in> nat ==> m dvd m";
by (fast_tac (claset() addIs [nat_1I, mult_1_right RS sym]) 1);
qed "dvd_refl";
Addsimps [dvd_refl];

Goalw [dvd_def] "[| m dvd n; n dvd p |] ==> m dvd p";
by (fast_tac (claset() addIs [mult_assoc, mult_type] ) 1);
qed "dvd_trans";

Goalw [dvd_def] "[| m dvd n; n dvd m |] ==> m=n";
by (fast_tac (claset() addDs [mult_eq_self_implies_10]
                    addss (simpset() addsimps [mult_assoc, mult_eq_1_iff])) 1);
qed "dvd_anti_sym";

Goalw [dvd_def] "[|(i#*j) dvd k; i \\<in> nat|] ==> i dvd k";
by (full_simp_tac (simpset() addsimps [mult_assoc]) 1);
by (Blast_tac 1);
qed "dvd_mult_left";

Goalw [dvd_def] "[|(i#*j) dvd k; j \\<in> nat|] ==> j dvd k";
by (Clarify_tac 1);
by (res_inst_tac [("x","i#*k")] bexI 1);
by (simp_tac (simpset() addsimps mult_ac) 1);
by (rtac mult_type 1); 
qed "dvd_mult_right";


(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(* GCD by Euclid's Algorithm *)

Goalw [gcd_def] "gcd(m,0) = natify(m)";
by (stac transrec 1);
by (Asm_simp_tac 1);
qed "gcd_0";
Addsimps [gcd_0];

Goal "gcd(natify(m),n) = gcd(m,n)";
by (simp_tac (simpset() addsimps [gcd_def]) 1); 
qed "gcd_natify1";

Goal "gcd(m, natify(n)) = gcd(m,n)";
by (simp_tac (simpset() addsimps [gcd_def]) 1); 
qed "gcd_natify2";
Addsimps [gcd_natify1,gcd_natify2];

Goalw [gcd_def]
    "[| 0<n;  n \\<in> nat |] ==> gcd(m,n) = gcd(n, m mod n)";
by (res_inst_tac [("P", "%z. ?left(z) = ?right")] (transrec RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [ltD RS mem_imp_not_eq RS not_sym,
                                      mod_less_divisor RS ltD]) 1);
qed "gcd_non_0_raw";

Goal "0 < natify(n) ==> gcd(m,n) = gcd(n, m mod n)";
by (cut_inst_tac [("m","m"),("n","natify(n)")] gcd_non_0_raw 1);
by Auto_tac; 
qed "gcd_non_0";

Goal "gcd(m,1) = 1";
by (asm_simp_tac (simpset() addsimps [gcd_non_0]) 1); 
qed "gcd_1";
Addsimps [gcd_1];

Goalw [dvd_def] "[| k dvd a; k dvd b |] ==> k dvd (a #+ b)";
by (fast_tac (claset() addIs [add_mult_distrib_left RS sym, add_type]) 1);
qed "dvd_add";

Goalw [dvd_def] "k dvd n ==> k dvd (m #* n)";
by (fast_tac (claset() addIs [mult_left_commute, mult_type]) 1);
qed "dvd_mult";

Goal "k dvd m ==> k dvd (m #* n)";
by (stac mult_commute 1); 
by (blast_tac (claset() addIs [dvd_mult]) 1); 
qed "dvd_mult2";

(* k dvd (m*k) *)
bind_thm ("dvdI1", dvd_refl RS dvd_mult);
bind_thm ("dvdI2", dvd_refl RS dvd_mult2);
Addsimps [dvdI1, dvdI2];

Goal "[| a \\<in> nat; b \\<in> nat; k dvd b; k dvd (a mod b) |] ==> k dvd a";
by (div_undefined_case_tac "b=0" 1);
by (blast_tac 
    (claset() addIs [mod_div_equality RS subst]
              addEs  [dvdE]
              addSIs [dvd_add, dvd_mult, mult_type,mod_type,div_type]) 1);
qed "dvd_mod_imp_dvd_raw";

Goal "[| k dvd (a mod b); k dvd b; a \\<in> nat |] ==> k dvd a";
by (cut_inst_tac [("b","natify(b)")] dvd_mod_imp_dvd_raw 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [dvd_def]) 1);  
qed "dvd_mod_imp_dvd";

(*Imitating TFL*)
Goal "[| n \\<in> nat; \
\        \\<forall>m \\<in> nat. P(m,0); \
\        \\<forall>m \\<in> nat. \\<forall>n \\<in> nat. 0<n --> P(n, m mod n) --> P(m,n) |] \
\     ==> \\<forall>m \\<in> nat. P (m,n)";
by (eres_inst_tac [("i","n")] complete_induct 1);
by (case_tac "x=0" 1);
by (Asm_simp_tac 1); 
by (Clarify_tac 1); 
by (dres_inst_tac [("x1","m"),("x","x")] (bspec RS bspec) 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [Ord_0_lt_iff])));
by (blast_tac (claset() addIs [mod_less_divisor RS ltD]) 1); 
qed_spec_mp "gcd_induct_lemma";

Goal "!!P. [| m \\<in> nat; n \\<in> nat; \
\        !!m. m \\<in> nat ==> P(m,0); \
\        !!m n. [|m \\<in> nat; n \\<in> nat; 0<n; P(n, m mod n)|] ==> P(m,n) |] \
\     ==> P (m,n)";
by (blast_tac (claset() addIs [gcd_induct_lemma]) 1); 
qed "gcd_induct"; 


(* gcd type *)

Goal "gcd(m, n) \\<in> nat";
by (subgoal_tac "gcd(natify(m), natify(n)) \\<in> nat" 1);
by (Asm_full_simp_tac 1); 
by (res_inst_tac [("m","natify(m)"),("n","natify(n)")] gcd_induct 1); 
by Auto_tac; 
by (asm_full_simp_tac (simpset() addsimps [gcd_non_0]) 1); 
qed "gcd_type";
Addsimps [gcd_type];

(* Property 1: gcd(a,b) divides a and b *)

Goal "[| m \\<in> nat; n \\<in> nat |] ==> gcd (m, n) dvd m & gcd (m, n) dvd n";
by (res_inst_tac [("m","m"),("n","n")] gcd_induct 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [gcd_non_0])));
by (blast_tac
    (claset() addIs [dvd_mod_imp_dvd_raw, nat_into_Ord RS Ord_0_lt]) 1);
qed "gcd_dvd_both";

Goal "m \\<in> nat ==> gcd(m,n) dvd m";
by (cut_inst_tac [("m","natify(m)"),("n","natify(n)")] gcd_dvd_both 1); 
by Auto_tac; 
qed "gcd_dvd1";
Addsimps [gcd_dvd1];

Goal "n \\<in> nat ==> gcd(m,n) dvd n";
by (cut_inst_tac [("m","natify(m)"),("n","natify(n)")] gcd_dvd_both 1); 
by Auto_tac; 
qed "gcd_dvd2";
Addsimps [gcd_dvd2];

(* if f divides a and b then f divides gcd(a,b) *)

Goalw [dvd_def] "[| f dvd a; f dvd b |] ==> f dvd (a mod b)";
by (div_undefined_case_tac "b=0" 1);
by Auto_tac;
by (blast_tac (claset() addIs [mod_mult_distrib2 RS sym]) 1);  
qed "dvd_mod";

(* Property 2: for all a,b,f naturals, 
               if f divides a and f divides b then f divides gcd(a,b)*)

Goal "[| m \\<in> nat; n \\<in> nat; f \\<in> nat |]   \
\     ==> (f dvd m) --> (f dvd n) --> f dvd gcd(m,n)";
by (res_inst_tac [("m","m"),("n","n")] gcd_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [gcd_non_0, dvd_mod])));
qed_spec_mp "gcd_greatest_raw";

Goal "[| f dvd m;  f dvd n;  f \\<in> nat |] ==> f dvd gcd(m,n)";
by (rtac gcd_greatest_raw 1); 
by (auto_tac (claset(), simpset() addsimps [dvd_def])); 
qed "gcd_greatest";

Goal "[| k \\<in> nat; m \\<in> nat; n \\<in> nat |] \
\     ==> (k dvd gcd (m, n)) <-> (k dvd m & k dvd n)";
by (blast_tac (claset() addSIs [gcd_greatest, gcd_dvd1, gcd_dvd2] 
                        addIs [dvd_trans]) 1); 
qed "gcd_greatest_iff";
Addsimps [gcd_greatest_iff];

(* GCD PROOF: GCD exists and gcd fits the definition *)

Goalw [is_gcd_def] "[| m \\<in> nat; n \\<in> nat |] ==> is_gcd(gcd(m,n), m, n)";
by (Asm_simp_tac 1);
qed "is_gcd";

(* GCD is unique *)

Goalw [is_gcd_def] "[|is_gcd(m,a,b); is_gcd(n,a,b); m\\<in>nat; n\\<in>nat|] ==> m=n";
by (blast_tac (claset() addIs [dvd_anti_sym]) 1);
qed "is_gcd_unique";

Goalw [is_gcd_def] "is_gcd(k,m,n) <-> is_gcd(k,n,m)";
by (Blast_tac 1); 
qed "is_gcd_commute";

Goal "[| m \\<in> nat; n \\<in> nat |] ==> gcd(m,n) = gcd(n,m)";
by (rtac is_gcd_unique 1); 
by (rtac is_gcd 1); 
by (rtac (is_gcd_commute RS iffD1) 3); 
by (rtac is_gcd 3); 
by Auto_tac; 
qed "gcd_commute_raw";

Goal "gcd(m,n) = gcd(n,m)";
by (cut_inst_tac [("m","natify(m)"),("n","natify(n)")] gcd_commute_raw 1); 
by Auto_tac; 
qed "gcd_commute";

Goal "[| k \\<in> nat; m \\<in> nat; n \\<in> nat |] \
\     ==> gcd (gcd (k, m), n) = gcd (k, gcd (m, n))";
by (rtac is_gcd_unique 1); 
by (rtac is_gcd 1); 
by (asm_full_simp_tac (simpset() addsimps [is_gcd_def]) 3);
by (blast_tac (claset() addIs [gcd_dvd1, gcd_dvd2, gcd_type] 
                        addIs [dvd_trans]) 3); 
by Auto_tac; 
qed "gcd_assoc_raw";

Goal "gcd (gcd (k, m), n) = gcd (k, gcd (m, n))";
by (cut_inst_tac [("k","natify(k)"),("m","natify(m)"),("n","natify(n)")] 
    gcd_assoc_raw 1); 
by Auto_tac; 
qed "gcd_assoc";

Goal "gcd (0, m) = natify(m)";
by (asm_simp_tac (simpset() addsimps [inst "m" "0" gcd_commute]) 1); 
qed "gcd_0_left"; 
Addsimps [gcd_0_left];

Goal "gcd (1, m) = 1";
by (asm_simp_tac (simpset() addsimps [inst "m" "1" gcd_commute]) 1); 
qed "gcd_1_left"; 
Addsimps [gcd_1_left];


(* Multiplication laws *)

Goal "[| k \\<in> nat; m \\<in> nat; n \\<in> nat |] \
\     ==> k #* gcd (m, n) = gcd (k #* m, k #* n)";
by (eres_inst_tac [("m","m"),("n","n")] gcd_induct 1); 
by (assume_tac 1); 
by (Asm_simp_tac 1); 
by (case_tac "k = 0" 1);
by (Asm_full_simp_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [mod_geq, gcd_non_0, 
                                    mod_mult_distrib2, Ord_0_lt_iff]) 1); 
qed "gcd_mult_distrib2_raw";

Goal "k #* gcd (m, n) = gcd (k #* m, k #* n)";
by (cut_inst_tac [("k","natify(k)"),("m","natify(m)"),("n","natify(n)")] 
    gcd_mult_distrib2_raw 1); 
by Auto_tac; 
qed "gcd_mult_distrib2";

Goal "gcd (k, k #* n) = natify(k)";
by (cut_inst_tac [("k","k"),("m","1"),("n","n")] gcd_mult_distrib2 1);
by Auto_tac; 
qed "gcd_mult";
Addsimps [gcd_mult];

Goal "gcd (k, k) = natify(k)";
by (cut_inst_tac [("k","k"),("n","1")] gcd_mult 1);
by Auto_tac; 
qed "gcd_self";
Addsimps [gcd_self];

Goal "[| gcd (k,n) = 1;  k dvd (m #* n);  m \\<in> nat |] \
\     ==> k dvd m";
by (cut_inst_tac [("k","m"),("m","k"),("n","n")] gcd_mult_distrib2 1);
by Auto_tac; 
by (eres_inst_tac [("b","m")] ssubst 1);
by (asm_full_simp_tac (simpset() addsimps [dvd_imp_nat1]) 1);  
qed "relprime_dvd_mult";

Goal "[| gcd (k,n) = 1;  m \\<in> nat |] \
\     ==> k dvd (m #* n) <-> k dvd m";
by (blast_tac (claset() addIs [dvdI2, relprime_dvd_mult, dvd_trans]) 1); 
qed "relprime_dvd_mult_iff";

Goalw [prime_def]
     "[| p \\<in> prime;  ~ (p dvd n);  n \\<in> nat |] ==> gcd (p, n) = 1";
by (Clarify_tac 1); 
by (dres_inst_tac [("x","gcd(p,n)")] bspec 1);
by Auto_tac;  
by (cut_inst_tac [("m","p"),("n","n")] gcd_dvd2 1);
by Auto_tac;
qed "prime_imp_relprime";

Goalw [prime_def] "p \\<in> prime ==> p \\<in> nat";
by Auto_tac; 
qed "prime_into_nat";

Goalw [prime_def] "p \\<in> prime \\<Longrightarrow> p\\<noteq>0";
by Auto_tac; 
qed "prime_nonzero";


(*This theorem leads immediately to a proof of the uniqueness of
  factorization.  If p divides a product of primes then it is
  one of those primes.*)

Goal "[|p dvd m #* n; p \\<in> prime; m \\<in> nat; n \\<in> nat |] ==> p dvd m \\<or> p dvd n";
by (blast_tac (claset() addIs [relprime_dvd_mult, prime_imp_relprime, 
                               prime_into_nat]) 1); 
qed "prime_dvd_mult";


(** Addition laws **)

Goal "gcd (m #+ n, n) = gcd (m, n)";
by (subgoal_tac "gcd (m #+ natify(n), natify(n)) = gcd (m, natify(n))" 1);
by (Asm_full_simp_tac 1); 
by (case_tac "natify(n) = 0" 1);
by (auto_tac (claset(), simpset() addsimps [Ord_0_lt_iff, gcd_non_0])); 
qed "gcd_add1"; 
Addsimps [gcd_add1];

Goal "gcd (m, m #+ n) = gcd (m, n)";
by (rtac (gcd_commute RS trans) 1); 
by (stac add_commute 1); 
by (Simp_tac 1);
by (rtac gcd_commute 1); 
qed "gcd_add2"; 
Addsimps [gcd_add2];

Goal "gcd (m, n #+ m) = gcd (m, n)";
by (stac add_commute 1); 
by (rtac gcd_add2 1); 
qed "gcd_add2'"; 
Addsimps [gcd_add2'];

Goal "k \\<in> nat ==> gcd (m, k #* m #+ n) = gcd (m, n)";
by (etac nat_induct 1); 
by (auto_tac (claset(), simpset() addsimps [gcd_add2, add_assoc])); 
qed "gcd_add_mult_raw";

Goal "gcd (m, k #* m #+ n) = gcd (m, n)";
by (cut_inst_tac [("k","natify(k)")] gcd_add_mult_raw 1);
by Auto_tac; 
qed "gcd_add_mult";


(* More multiplication laws *)

Goal "[|gcd (k,n) = 1; m \\<in> nat; n \\<in> nat|] ==> gcd (k #* m, n) = gcd (m, n)";
by (rtac dvd_anti_sym 1);
 by (rtac gcd_greatest 1);
  by (rtac (inst "n" "k" relprime_dvd_mult) 1);
by (asm_full_simp_tac (simpset() addsimps [gcd_assoc]) 1); 
by (asm_full_simp_tac (simpset() addsimps [gcd_commute]) 1); 
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [mult_commute])));
by (blast_tac (claset() addIs [dvdI1, gcd_dvd1, dvd_trans]) 1); 
qed "gcd_mult_cancel_raw";


Goal "gcd (k,n) = 1 ==> gcd (k #* m, n) = gcd (m, n)";
by (cut_inst_tac [("m","natify(m)"),("n","natify(n)")] gcd_mult_cancel_raw 1); 
by Auto_tac; 
qed "gcd_mult_cancel";


(*** The square root of a prime is irrational: key lemma ***)

Goal "\\<lbrakk>n#*n = p#*(k#*k); p \\<in> prime; n \\<in> nat\\<rbrakk> \\<Longrightarrow> p dvd n";
by (subgoal_tac "p dvd n#*n" 1); 
 by (blast_tac (claset() addDs [prime_dvd_mult]) 1);
by (res_inst_tac [("j","k#*k")] dvd_mult_left 1);
 by (auto_tac (claset(), simpset() addsimps [prime_def])); 
qed "prime_dvd_other_side";

Goal "\\<lbrakk>k#*k = p#*(j#*j); p \\<in> prime; 0 < k; j \\<in> nat; k \\<in> nat\\<rbrakk> \
\     \\<Longrightarrow> k < p#*j & 0 < j";
by (rtac ccontr 1);
by (asm_full_simp_tac (simpset() addsimps [not_lt_iff_le, prime_into_nat]) 1); 
by (etac disjE 1);
 by (ftac mult_le_mono 1 THEN REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps mult_ac) 1);
by (auto_tac (claset() addSDs [natify_eqE], 
              simpset() addsimps [not_lt_iff_le, prime_into_nat, 
                                  mult_le_cancel_le1])); 
by (asm_full_simp_tac (simpset() addsimps [prime_def]) 1); 
by (blast_tac (claset() addDs [lt_trans1]) 1); 
qed "reduction";


Goal "j #* (p#*j) = k#*k \\<Longrightarrow> k#*k = p#*(j#*j)";
by (asm_full_simp_tac (simpset() addsimps mult_ac) 1); 
qed "rearrange";

Goal "\\<lbrakk>m \\<in> nat; p \\<in> prime\\<rbrakk> \\<Longrightarrow> \\<forall>k \\<in> nat. 0<k \\<longrightarrow> m#*m \\<noteq> p#*(k#*k)";
by (etac complete_induct 1); 
by (Clarify_tac 1); 
by (ftac prime_dvd_other_side 1);
by (assume_tac 1); 
by (assume_tac 1); 
by (etac dvdE 1);
by (asm_full_simp_tac (simpset() addsimps [mult_assoc, mult_cancel1, 
                                           prime_nonzero, prime_into_nat]) 1); 
by (blast_tac (claset() addDs [rearrange, reduction, ltD]) 1); 
qed "prime_not_square";
