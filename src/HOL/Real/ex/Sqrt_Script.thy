(*  Title:      HOL/Real/ex/Sqrt_Script.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header {*  Square roots of primes are irrational *}

text {*
  \medskip Contrast this linear Isar script with Markus Wenzel's 
           more mathematical version.
*}

theory Sqrt_Script = Primes + Real:

section {* Preliminaries *}

lemma prime_nonzero:  "p \<in> prime \<Longrightarrow> p\<noteq>0"
by (force simp add: prime_def)

lemma prime_dvd_other_side: "\<lbrakk>n*n = p*(k*k); p \<in> prime\<rbrakk> \<Longrightarrow> p dvd n"
apply (subgoal_tac "p dvd n*n", blast dest: prime_dvd_mult)
apply (rule_tac j="k*k" in dvd_mult_left, simp)
done

lemma reduction: "\<lbrakk>p \<in> prime; 0 < k; k*k = p*(j*j)\<rbrakk> \<Longrightarrow> k < p*j & 0 < j"
apply (rule ccontr)
apply (simp add: linorder_not_less)
apply (erule disjE)
 apply (frule mult_le_mono, assumption)
 apply auto
apply (force simp add: prime_def)
done

lemma rearrange: "(j::nat) * (p*j) = k*k \<Longrightarrow> k*k = p*(j*j)"
by (simp add: mult_ac)

lemma prime_not_square [rule_format]:
     "p \<in> prime \<Longrightarrow> \<forall>k. 0<k \<longrightarrow> m*m \<noteq> p*(k*k)"
apply (induct_tac m rule: nat_less_induct)
apply clarify 
apply (frule prime_dvd_other_side, assumption)
apply (erule dvdE)
apply (simp add: nat_mult_eq_cancel_disj prime_nonzero)
apply (blast dest: rearrange reduction)
done


section {* The set of rational numbers [Borrowed from Markus Wenzel] *}

constdefs
  rationals :: "real set"    ("\<rat>")
  "\<rat> \<equiv> {x. \<exists>m n. n \<noteq> 0 \<and> \<bar>x\<bar> = real (m::nat) / real (n::nat)}"


section {* Main theorem *}

text {*
  \tweakskip The square root of any prime number (including @{text 2})
  is irrational.
*}

theorem prime_sqrt_irrational: "\<lbrakk>p \<in> prime; x*x = real p; 0 \<le> x\<rbrakk> \<Longrightarrow> x \<notin> \<rat>"
apply (simp add: rationals_def real_abs_def)
apply clarify
apply (erule_tac P="real m / real n * ?x = ?y" in rev_mp) 
apply (simp del: real_of_nat_mult
	    add: real_divide_eq_eq prime_not_square
                 real_of_nat_mult [THEN sym])
done

lemma two_is_prime: "2 \<in> prime"
apply (auto simp add: prime_def)
apply (case_tac "m")
apply (auto dest!: dvd_imp_le)
apply arith
done

lemmas two_sqrt_irrational = prime_sqrt_irrational [OF two_is_prime]

end
