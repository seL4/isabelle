(*  Title:      ZF/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm
*)

theory Primes = Main:
constdefs
  divides :: "[i,i]=>o"              (infixl "dvd" 50) 
    "m dvd n == m \<in> nat & n \<in> nat & (\<exists>k \<in> nat. n = m#*k)"

  is_gcd  :: "[i,i,i]=>o"            (* great common divisor *)
    "is_gcd(p,m,n) == ((p dvd m) & (p dvd n))   &
                       (\<forall>d\<in>nat. (d dvd m) & (d dvd n) --> d dvd p)"

  gcd     :: "[i,i]=>i"              (* gcd by Euclid's algorithm *)
    "gcd(m,n) == transrec(natify(n),
			%n f. \<lambda>m \<in> nat.
			        if n=0 then m else f`(m mod n)`n) ` natify(m)"

  coprime :: "[i,i]=>o"              (* coprime relation *)
    "coprime(m,n) == gcd(m,n) = 1"
  
  prime   :: i                     (* set of prime numbers *)
   "prime == {p \<in> nat. 1<p & (\<forall>m \<in> nat. m dvd p --> m=1 | m=p)}"

(************************************************)
(** Divides Relation                           **)
(************************************************)

lemma dvdD: "m dvd n ==> m \<in> nat & n \<in> nat & (\<exists>k \<in> nat. n = m#*k)"
apply (unfold divides_def)
apply assumption
done

lemma dvdE:
     "[|m dvd n;  !!k. [|m \<in> nat; n \<in> nat; k \<in> nat; n = m#*k|] ==> P|] ==> P"
by (blast dest!: dvdD)

lemmas dvd_imp_nat1 = dvdD [THEN conjunct1, standard]
lemmas dvd_imp_nat2 = dvdD [THEN conjunct2, THEN conjunct1, standard]


lemma dvd_0_right [simp]: "m \<in> nat ==> m dvd 0"
apply (unfold divides_def)
apply (fast intro: nat_0I mult_0_right [symmetric])
done

lemma dvd_0_left: "0 dvd m ==> m = 0"
by (unfold divides_def, force)

lemma dvd_refl [simp]: "m \<in> nat ==> m dvd m"
apply (unfold divides_def)
apply (fast intro: nat_1I mult_1_right [symmetric])
done

lemma dvd_trans: "[| m dvd n; n dvd p |] ==> m dvd p"
apply (unfold divides_def)
apply (fast intro: mult_assoc mult_type)
done

lemma dvd_anti_sym: "[| m dvd n; n dvd m |] ==> m=n"
apply (unfold divides_def)
apply (force dest: mult_eq_self_implies_10
             simp add: mult_assoc mult_eq_1_iff)
done

lemma dvd_mult_left: "[|(i#*j) dvd k; i \<in> nat|] ==> i dvd k"
apply (unfold divides_def)
apply (simp add: mult_assoc)
apply blast
done

lemma dvd_mult_right: "[|(i#*j) dvd k; j \<in> nat|] ==> j dvd k"
apply (unfold divides_def)
apply clarify
apply (rule_tac x = "i#*k" in bexI)
apply (simp add: mult_ac)
apply (rule mult_type)
done


(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(* GCD by Euclid's Algorithm *)

lemma gcd_0 [simp]: "gcd(m,0) = natify(m)"
apply (unfold gcd_def)
apply (subst transrec)
apply simp
done

lemma gcd_natify1 [simp]: "gcd(natify(m),n) = gcd(m,n)"
by (simp add: gcd_def)

lemma gcd_natify2 [simp]: "gcd(m, natify(n)) = gcd(m,n)"
by (simp add: gcd_def)

lemma gcd_non_0_raw: 
    "[| 0<n;  n \<in> nat |] ==> gcd(m,n) = gcd(n, m mod n)"
apply (unfold gcd_def)
apply (rule_tac P = "%z. ?left (z) = ?right" in transrec [THEN ssubst])
apply (simp add: ltD [THEN mem_imp_not_eq, THEN not_sym] 
                 mod_less_divisor [THEN ltD])
done

lemma gcd_non_0: "0 < natify(n) ==> gcd(m,n) = gcd(n, m mod n)"
apply (cut_tac m = "m" and n = "natify (n) " in gcd_non_0_raw)
apply auto
done

lemma gcd_1 [simp]: "gcd(m,1) = 1"
by (simp (no_asm_simp) add: gcd_non_0)

lemma dvd_add: "[| k dvd a; k dvd b |] ==> k dvd (a #+ b)"
apply (unfold divides_def)
apply (fast intro: add_mult_distrib_left [symmetric] add_type)
done

lemma dvd_mult: "k dvd n ==> k dvd (m #* n)"
apply (unfold divides_def)
apply (fast intro: mult_left_commute mult_type)
done

lemma dvd_mult2: "k dvd m ==> k dvd (m #* n)"
apply (subst mult_commute)
apply (blast intro: dvd_mult)
done

(* k dvd (m*k) *)
lemmas dvdI1 [simp] = dvd_refl [THEN dvd_mult, standard]
lemmas dvdI2 [simp] = dvd_refl [THEN dvd_mult2, standard]

lemma dvd_mod_imp_dvd_raw:
     "[| a \<in> nat; b \<in> nat; k dvd b; k dvd (a mod b) |] ==> k dvd a"
apply (case_tac "b=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (blast intro: mod_div_equality [THEN subst]
             elim: dvdE 
             intro!: dvd_add dvd_mult mult_type mod_type div_type)
done

lemma dvd_mod_imp_dvd: "[| k dvd (a mod b); k dvd b; a \<in> nat |] ==> k dvd a"
apply (cut_tac b = "natify (b)" in dvd_mod_imp_dvd_raw)
apply auto
apply (simp add: divides_def)
done

(*Imitating TFL*)
lemma gcd_induct_lemma [rule_format (no_asm)]: "[| n \<in> nat;  
         \<forall>m \<in> nat. P(m,0);  
         \<forall>m \<in> nat. \<forall>n \<in> nat. 0<n --> P(n, m mod n) --> P(m,n) |]  
      ==> \<forall>m \<in> nat. P (m,n)"
apply (erule_tac i = "n" in complete_induct)
apply (case_tac "x=0")
apply (simp (no_asm_simp))
apply clarify
apply (drule_tac x1 = "m" and x = "x" in bspec [THEN bspec])
apply (simp_all add: Ord_0_lt_iff)
apply (blast intro: mod_less_divisor [THEN ltD])
done

lemma gcd_induct: "!!P. [| m \<in> nat; n \<in> nat;  
         !!m. m \<in> nat ==> P(m,0);  
         !!m n. [|m \<in> nat; n \<in> nat; 0<n; P(n, m mod n)|] ==> P(m,n) |]  
      ==> P (m,n)"
by (blast intro: gcd_induct_lemma)



(* gcd type *)

lemma gcd_type [simp,TC]: "gcd(m, n) \<in> nat"
apply (subgoal_tac "gcd (natify (m) , natify (n)) \<in> nat")
apply simp
apply (rule_tac m = "natify (m)" and n = "natify (n)" in gcd_induct)
apply auto
apply (simp add: gcd_non_0)
done


(* Property 1: gcd(a,b) divides a and b *)

lemma gcd_dvd_both:
     "[| m \<in> nat; n \<in> nat |] ==> gcd (m, n) dvd m & gcd (m, n) dvd n"
apply (rule_tac m = "m" and n = "n" in gcd_induct)
apply (simp_all add: gcd_non_0)
apply (blast intro: dvd_mod_imp_dvd_raw nat_into_Ord [THEN Ord_0_lt])
done

lemma gcd_dvd1 [simp]: "m \<in> nat ==> gcd(m,n) dvd m"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_dvd_both)
apply auto
done

lemma gcd_dvd2 [simp]: "n \<in> nat ==> gcd(m,n) dvd n"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_dvd_both)
apply auto
done

(* if f divides a and b then f divides gcd(a,b) *)

lemma dvd_mod: "[| f dvd a; f dvd b |] ==> f dvd (a mod b)"
apply (unfold divides_def)
apply (case_tac "b=0")
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply auto
apply (blast intro: mod_mult_distrib2 [symmetric])
done

(* Property 2: for all a,b,f naturals, 
               if f divides a and f divides b then f divides gcd(a,b)*)

lemma gcd_greatest_raw [rule_format]:
     "[| m \<in> nat; n \<in> nat; f \<in> nat |]    
      ==> (f dvd m) --> (f dvd n) --> f dvd gcd(m,n)"
apply (rule_tac m = "m" and n = "n" in gcd_induct)
apply (simp_all add: gcd_non_0 dvd_mod)
done

lemma gcd_greatest: "[| f dvd m;  f dvd n;  f \<in> nat |] ==> f dvd gcd(m,n)"
apply (rule gcd_greatest_raw)
apply (auto simp add: divides_def)
done

lemma gcd_greatest_iff [simp]: "[| k \<in> nat; m \<in> nat; n \<in> nat |]  
      ==> (k dvd gcd (m, n)) <-> (k dvd m & k dvd n)"
by (blast intro!: gcd_greatest gcd_dvd1 gcd_dvd2 intro: dvd_trans)


(* GCD PROOF: GCD exists and gcd fits the definition *)

lemma is_gcd: "[| m \<in> nat; n \<in> nat |] ==> is_gcd(gcd(m,n), m, n)"
by (simp add: is_gcd_def)

(* GCD is unique *)

lemma is_gcd_unique: "[|is_gcd(m,a,b); is_gcd(n,a,b); m\<in>nat; n\<in>nat|] ==> m=n"
apply (unfold is_gcd_def)
apply (blast intro: dvd_anti_sym)
done

lemma is_gcd_commute: "is_gcd(k,m,n) <-> is_gcd(k,n,m)"
by (unfold is_gcd_def, blast)

lemma gcd_commute_raw: "[| m \<in> nat; n \<in> nat |] ==> gcd(m,n) = gcd(n,m)"
apply (rule is_gcd_unique)
apply (rule is_gcd)
apply (rule_tac [3] is_gcd_commute [THEN iffD1])
apply (rule_tac [3] is_gcd)
apply auto
done

lemma gcd_commute: "gcd(m,n) = gcd(n,m)"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_commute_raw)
apply auto
done

lemma gcd_assoc_raw: "[| k \<in> nat; m \<in> nat; n \<in> nat |]  
      ==> gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
apply (rule is_gcd_unique)
apply (rule is_gcd)
apply (simp_all add: is_gcd_def)
apply (blast intro: gcd_dvd1 gcd_dvd2 gcd_type intro: dvd_trans)
done

lemma gcd_assoc: "gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
apply (cut_tac k = "natify (k)" and m = "natify (m)" and n = "natify (n) " 
       in gcd_assoc_raw)
apply auto
done

lemma gcd_0_left [simp]: "gcd (0, m) = natify(m)"
by (simp add: gcd_commute [of 0])

lemma gcd_1_left [simp]: "gcd (1, m) = 1"
by (simp add: gcd_commute [of 1])


(* Multiplication laws *)

lemma gcd_mult_distrib2_raw:
     "[| k \<in> nat; m \<in> nat; n \<in> nat |]  
      ==> k #* gcd (m, n) = gcd (k #* m, k #* n)"
apply (erule_tac m = "m" and n = "n" in gcd_induct)
apply assumption
apply (simp)
apply (case_tac "k = 0")
apply simp
apply (simp add: mod_geq gcd_non_0 mod_mult_distrib2 Ord_0_lt_iff)
done

lemma gcd_mult_distrib2: "k #* gcd (m, n) = gcd (k #* m, k #* n)"
apply (cut_tac k = "natify (k)" and m = "natify (m)" and n = "natify (n) " 
       in gcd_mult_distrib2_raw)
apply auto
done

lemma gcd_mult [simp]: "gcd (k, k #* n) = natify(k)"
apply (cut_tac k = "k" and m = "1" and n = "n" in gcd_mult_distrib2)
apply auto
done

lemma gcd_self [simp]: "gcd (k, k) = natify(k)"
apply (cut_tac k = "k" and n = "1" in gcd_mult)
apply auto
done

lemma relprime_dvd_mult:
     "[| gcd (k,n) = 1;  k dvd (m #* n);  m \<in> nat |] ==> k dvd m"
apply (cut_tac k = "m" and m = "k" and n = "n" in gcd_mult_distrib2)
apply auto
apply (erule_tac b = "m" in ssubst)
apply (simp add: dvd_imp_nat1)
done

lemma relprime_dvd_mult_iff:
     "[| gcd (k,n) = 1;  m \<in> nat |] ==> k dvd (m #* n) <-> k dvd m"
by (blast intro: dvdI2 relprime_dvd_mult dvd_trans)

lemma prime_imp_relprime: 
     "[| p \<in> prime;  ~ (p dvd n);  n \<in> nat |] ==> gcd (p, n) = 1"
apply (unfold prime_def)
apply clarify
apply (drule_tac x = "gcd (p,n)" in bspec)
apply auto
apply (cut_tac m = "p" and n = "n" in gcd_dvd2)
apply auto
done

lemma prime_into_nat: "p \<in> prime ==> p \<in> nat"
by (unfold prime_def, auto)

lemma prime_nonzero: "p \<in> prime \<Longrightarrow> p\<noteq>0"
by (unfold prime_def, auto)


(*This theorem leads immediately to a proof of the uniqueness of
  factorization.  If p divides a product of primes then it is
  one of those primes.*)

lemma prime_dvd_mult:
     "[|p dvd m #* n; p \<in> prime; m \<in> nat; n \<in> nat |] ==> p dvd m \<or> p dvd n"
by (blast intro: relprime_dvd_mult prime_imp_relprime prime_into_nat)


(** Addition laws **)

lemma gcd_add1 [simp]: "gcd (m #+ n, n) = gcd (m, n)"
apply (subgoal_tac "gcd (m #+ natify (n) , natify (n)) = gcd (m, natify (n))")
apply simp
apply (case_tac "natify (n) = 0")
apply (auto simp add: Ord_0_lt_iff gcd_non_0)
done

lemma gcd_add2 [simp]: "gcd (m, m #+ n) = gcd (m, n)"
apply (rule gcd_commute [THEN trans])
apply (subst add_commute)
apply simp
apply (rule gcd_commute)
done

lemma gcd_add2' [simp]: "gcd (m, n #+ m) = gcd (m, n)"
by (subst add_commute, rule gcd_add2)

lemma gcd_add_mult_raw: "k \<in> nat ==> gcd (m, k #* m #+ n) = gcd (m, n)"
apply (erule nat_induct)
apply (auto simp add: gcd_add2 add_assoc)
done

lemma gcd_add_mult: "gcd (m, k #* m #+ n) = gcd (m, n)"
apply (cut_tac k = "natify (k)" in gcd_add_mult_raw)
apply auto
done


(* More multiplication laws *)

lemma gcd_mult_cancel_raw:
     "[|gcd (k,n) = 1; m \<in> nat; n \<in> nat|] ==> gcd (k #* m, n) = gcd (m, n)"
apply (rule dvd_anti_sym)
 apply (rule gcd_greatest)
  apply (rule relprime_dvd_mult [of _ k])
apply (simp add: gcd_assoc)
apply (simp add: gcd_commute)
apply (simp_all add: mult_commute)
apply (blast intro: dvdI1 gcd_dvd1 dvd_trans)
done

lemma gcd_mult_cancel: "gcd (k,n) = 1 ==> gcd (k #* m, n) = gcd (m, n)"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_mult_cancel_raw)
apply auto
done


(*** The square root of a prime is irrational: key lemma ***)

lemma prime_dvd_other_side:
     "\<lbrakk>n#*n = p#*(k#*k); p \<in> prime; n \<in> nat\<rbrakk> \<Longrightarrow> p dvd n"
apply (subgoal_tac "p dvd n#*n")
 apply (blast dest: prime_dvd_mult)
apply (rule_tac j = "k#*k" in dvd_mult_left)
 apply (auto simp add: prime_def)
done

lemma reduction:
     "\<lbrakk>k#*k = p#*(j#*j); p \<in> prime; 0 < k; j \<in> nat; k \<in> nat\<rbrakk>  
      \<Longrightarrow> k < p#*j & 0 < j"
apply (rule ccontr)
apply (simp add: not_lt_iff_le prime_into_nat)
apply (erule disjE)
 apply (frule mult_le_mono, assumption+)
apply (simp add: mult_ac)
apply (auto dest!: natify_eqE 
            simp add: not_lt_iff_le prime_into_nat mult_le_cancel_le1)
apply (simp add: prime_def)
apply (blast dest: lt_trans1)
done

lemma rearrange: "j #* (p#*j) = k#*k \<Longrightarrow> k#*k = p#*(j#*j)"
by (simp add: mult_ac)

lemma prime_not_square:
     "\<lbrakk>m \<in> nat; p \<in> prime\<rbrakk> \<Longrightarrow> \<forall>k \<in> nat. 0<k \<longrightarrow> m#*m \<noteq> p#*(k#*k)"
apply (erule complete_induct)
apply clarify
apply (frule prime_dvd_other_side)
apply assumption
apply assumption
apply (erule dvdE)
apply (simp add: mult_assoc mult_cancel1 prime_nonzero prime_into_nat)
apply (blast dest: rearrange reduction ltD)
done

end
