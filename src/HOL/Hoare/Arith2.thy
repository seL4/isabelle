(*  Title:      HOL/Hoare/Arith2.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic.  Much of this duplicates ex/Primes.
*)

theory Arith2
imports Main
begin

constdefs
  "cd"    :: "[nat, nat, nat] => bool"
  "cd x m n  == x dvd m & x dvd n"

  gcd     :: "[nat, nat] => nat"
  "gcd m n     == @x.(cd x m n) & (!y.(cd y m n) --> y<=x)"

consts fac     :: "nat => nat"

primrec
  "fac 0 = Suc 0"
  "fac(Suc n) = (Suc n)*fac(n)"


subsubsection {* cd *}

lemma cd_nnn: "0<n ==> cd n n n"
  apply (simp add: cd_def)
  done

lemma cd_le: "[| cd x m n; 0<m; 0<n |] ==> x<=m & x<=n"
  apply (unfold cd_def)
  apply (blast intro: dvd_imp_le)
  done

lemma cd_swap: "cd x m n = cd x n m"
  apply (unfold cd_def)
  apply blast
  done

lemma cd_diff_l: "n<=m ==> cd x m n = cd x (m-n) n"
  apply (unfold cd_def)
  apply (fastsimp dest: dvd_diffD)
  done

lemma cd_diff_r: "m<=n ==> cd x m n = cd x m (n-m)"
  apply (unfold cd_def)
  apply (fastsimp dest: dvd_diffD)
  done


subsubsection {* gcd *}

lemma gcd_nnn: "0<n ==> n = gcd n n"
  apply (unfold gcd_def)
  apply (frule cd_nnn)
  apply (rule some_equality [symmetric])
  apply (blast dest: cd_le)
  apply (blast intro: le_anti_sym dest: cd_le)
  done

lemma gcd_swap: "gcd m n = gcd n m"
  apply (simp add: gcd_def cd_swap)
  done

lemma gcd_diff_l: "n<=m ==> gcd m n = gcd (m-n) n"
  apply (unfold gcd_def)
  apply (subgoal_tac "n<=m ==> !x. cd x m n = cd x (m-n) n")
  apply simp
  apply (rule allI)
  apply (erule cd_diff_l)
  done

lemma gcd_diff_r: "m<=n ==> gcd m n = gcd m (n-m)"
  apply (unfold gcd_def)
  apply (subgoal_tac "m<=n ==> !x. cd x m n = cd x m (n-m) ")
  apply simp
  apply (rule allI)
  apply (erule cd_diff_r)
  done


subsubsection {* pow *}

lemma sq_pow_div2 [simp]:
    "m mod 2 = 0 ==> ((n::nat)*n)^(m div 2) = n^m"
  apply (simp add: power2_eq_square [symmetric] power_mult [symmetric] mult_div_cancel)
  done

end
