(*  Title:      HOL/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The Greatest Common Divisor and Euclid's algorithm

See H. Davenport, "The Higher Arithmetic".  6th edition.  (CUP, 1992)
*)

theory Primes = Main:
consts
  gcd     :: "nat*nat=>nat"               (*Euclid's algorithm *)

recdef gcd "measure ((%(m,n).n) ::nat*nat=>nat)"
    "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))"

constdefs
  is_gcd  :: "[nat,nat,nat]=>bool"        (*gcd as a relation*)
    "is_gcd p m n == p dvd m  &  p dvd n  &
                     (ALL d. d dvd m & d dvd n --> d dvd p)"

  coprime :: "[nat,nat]=>bool"
    "coprime m n == gcd(m,n) = 1"

  prime   :: "nat set"
    "prime == {p. 1<p & (ALL m. m dvd p --> m=1 | m=p)}"


(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(*** Euclid's Algorithm ***)


lemma gcd_induct:
     "[| !!m. P m 0;     
         !!m n. [| 0<n;  P n (m mod n) |] ==> P m n  
      |] ==> P (m::nat) (n::nat)"
  apply (rule_tac u="m" and v="n" in gcd.induct)
  apply (case_tac "n=0")
  apply (simp_all)
  done


lemma gcd_0 [simp]: "gcd(m,0) = m"
  apply (simp);
  done

lemma gcd_non_0: "0<n ==> gcd(m,n) = gcd (n, m mod n)"
  apply (simp)
  done;

declare gcd.simps [simp del];

lemma gcd_1 [simp]: "gcd(m,1) = 1"
  apply (simp add: gcd_non_0)
  done

(*gcd(m,n) divides m and n.  The conjunctions don't seem provable separately*)
lemma gcd_dvd_both: "(gcd(m,n) dvd m) & (gcd(m,n) dvd n)"
  apply (rule_tac m="m" and n="n" in gcd_induct)
  apply (simp_all add: gcd_non_0)
  apply (blast dest: dvd_mod_imp_dvd)
  done

lemmas gcd_dvd1 = gcd_dvd_both [THEN conjunct1];
lemmas gcd_dvd2 = gcd_dvd_both [THEN conjunct2];


(*Maximality: for all m,n,f naturals, 
                if f divides m and f divides n then f divides gcd(m,n)*)
lemma gcd_greatest [rulify]: "(f dvd m) --> (f dvd n) --> f dvd gcd(m,n)"
  apply (rule_tac m="m" and n="n" in gcd_induct)
  apply (simp_all add: gcd_non_0 dvd_mod);
  done;

(*Function gcd yields the Greatest Common Divisor*)
lemma is_gcd: "is_gcd (gcd(m,n)) m n"
  apply (simp add: is_gcd_def gcd_greatest gcd_dvd_both);
  done

(*uniqueness of GCDs*)
lemma is_gcd_unique: "[| is_gcd m a b; is_gcd n a b |] ==> m=n"
  apply (simp add: is_gcd_def);
  apply (blast intro: dvd_anti_sym)
  done

lemma is_gcd_dvd: "[| is_gcd m a b; k dvd a; k dvd b |] ==> k dvd m"
  apply (auto simp add: is_gcd_def);
  done

(** Commutativity **)

lemma is_gcd_commute: "is_gcd k m n = is_gcd k n m"
  apply (auto simp add: is_gcd_def);
  done

lemma gcd_commute: "gcd(m,n) = gcd(n,m)"
  apply (rule is_gcd_unique)
  apply (rule is_gcd)
  apply (subst is_gcd_commute)
  apply (simp add: is_gcd)
  done

lemma gcd_assoc: "gcd(gcd(k,m),n) = gcd(k,gcd(m,n))"
  apply (rule is_gcd_unique)
  apply (rule is_gcd)
  apply (simp add: is_gcd_def);
  apply (blast intro!: gcd_dvd1 gcd_dvd2 intro: dvd_trans gcd_greatest);
  done 

lemma gcd_0_left [simp]: "gcd(0,m) = m"
  apply (simp add: gcd_commute [of 0])
  done

lemma gcd_1_left [simp]: "gcd(1,m) = 1"
  apply (simp add: gcd_commute [of 1])
  done


(** Multiplication laws **)

(*Davenport, page 27*)
lemma gcd_mult_distrib2: "k * gcd(m,n) = gcd(k*m, k*n)"
  apply (rule_tac m="m" and n="n" in gcd_induct)
  apply (simp)
  apply (case_tac "k=0")
  apply (simp_all add: mod_geq gcd_non_0 mod_mult_distrib2)
  done

lemma gcd_self [simp]: "gcd(m,m) = m"
  apply (cut_tac k="m" and m="1" and n="1" in gcd_mult_distrib2)
  apply (simp)
(*alternative:
proof -;
  note gcd_mult_distrib2 [of m 1 1, simplify, THEN sym];
      thus ?thesis; by assumption; qed; *)
done

lemma gcd_mult [simp]: "gcd(k, k*n) = k"
  apply (cut_tac k="k" and m="1" and n="n" in gcd_mult_distrib2)
  apply (simp)
(*alternative:
proof -;
  note gcd_mult_distrib2 [of k 1 n, simplify, THEN sym];
      thus ?thesis; by assumption; qed; *)
done

lemma relprime_dvd_mult: "[| gcd(k,n)=1; k dvd (m*n) |] ==> k dvd m";
  apply (subgoal_tac "k dvd gcd(m*k, m*n)")
   apply (subgoal_tac "gcd(m*k, m*n) = m")
    apply (simp)
   apply (simp add: gcd_mult_distrib2 [THEN sym]);
  apply (rule gcd_greatest)
   apply (simp_all)
  done

lemma prime_imp_relprime: "[| p: prime;  ~ p dvd n |] ==> gcd (p, n) = 1"
  apply (simp add: prime_def);
  apply (cut_tac m="p" and n="n" in gcd_dvd_both)
  apply auto
  done

(*This theorem leads immediately to a proof of the uniqueness of factorization.
  If p divides a product of primes then it is one of those primes.*)
lemma prime_dvd_mult: "[| p: prime; p dvd (m*n) |] ==> p dvd m | p dvd n"
  apply (blast intro: relprime_dvd_mult prime_imp_relprime)
  done


(** Addition laws **)

lemma gcd_add1 [simp]: "gcd(m+n, n) = gcd(m,n)"
  apply (case_tac "n=0")
  apply (simp_all add: gcd_non_0)
  done

lemma gcd_add2 [simp]: "gcd(m, m+n) = gcd(m,n)"
  apply (rule gcd_commute [THEN trans])
  apply (subst add_commute)
  apply (simp add: gcd_add1)
  apply (rule gcd_commute)
  done

lemma gcd_add2' [simp]: "gcd(m, n+m) = gcd(m,n)"
  apply (subst add_commute)
  apply (rule gcd_add2)
  done

lemma gcd_add_mult: "gcd(m, k*m+n) = gcd(m,n)"
  apply (induct_tac "k")
  apply (simp_all add: gcd_add2 add_assoc)
  done


(** More multiplication laws **)

lemma gcd_dvd_gcd_mult: "gcd(m,n) dvd gcd(k*m, n)"
  apply (blast intro: gcd_dvd2 gcd_dvd1 dvd_trans gcd_greatest);
  done

lemma gcd_mult_cancel: "gcd(k,n) = 1 ==> gcd(k*m, n) = gcd(m,n)"
  apply (rule dvd_anti_sym)
   apply (rule gcd_greatest)
    apply (rule_tac n="k" in relprime_dvd_mult)
     apply (simp add: gcd_assoc)
     apply (simp add: gcd_commute)
    apply (simp_all add: mult_commute gcd_dvd1 gcd_dvd2 gcd_dvd_gcd_mult)
  done

end
