(*  Title:      HOL/Hoare/Arith2.thy
    Author:     Norbert Galm
    Copyright   1995 TUM
*)

section \<open>More arithmetic\<close>

theory Arith2
  imports Main
begin

definition cd :: "[nat, nat, nat] \<Rightarrow> bool"
  where "cd x m n \<longleftrightarrow> x dvd m \<and> x dvd n"

definition gcd :: "[nat, nat] \<Rightarrow> nat"
  where "gcd m n = (SOME x. cd x m n & (\<forall>y.(cd y m n) \<longrightarrow> y\<le>x))"

primrec fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = Suc 0"
| "fac (Suc n) = Suc n * fac n"


subsection \<open>cd\<close>

lemma cd_nnn: "0<n \<Longrightarrow> cd n n n"
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

lemma cd_diff_l: "n\<le>m \<Longrightarrow> cd x m n = cd x (m-n) n"
  apply (unfold cd_def)
  apply (fastforce dest: dvd_diffD)
  done

lemma cd_diff_r: "m\<le>n \<Longrightarrow> cd x m n = cd x m (n-m)"
  apply (unfold cd_def)
  apply (fastforce dest: dvd_diffD)
  done


subsection \<open>gcd\<close>

lemma gcd_nnn: "0<n \<Longrightarrow> n = gcd n n"
  apply (unfold gcd_def)
  apply (frule cd_nnn)
  apply (rule some_equality [symmetric])
  apply (blast dest: cd_le)
  apply (blast intro: le_antisym dest: cd_le)
  done

lemma gcd_swap: "gcd m n = gcd n m"
  apply (simp add: gcd_def cd_swap)
  done

lemma gcd_diff_l: "n\<le>m \<Longrightarrow> gcd m n = gcd (m-n) n"
  apply (unfold gcd_def)
  apply (subgoal_tac "n\<le>m \<Longrightarrow> \<forall>x. cd x m n = cd x (m-n) n")
  apply simp
  apply (rule allI)
  apply (erule cd_diff_l)
  done

lemma gcd_diff_r: "m\<le>n \<Longrightarrow> gcd m n = gcd m (n-m)"
  apply (unfold gcd_def)
  apply (subgoal_tac "m\<le>n \<Longrightarrow> \<forall>x. cd x m n = cd x m (n-m) ")
  apply simp
  apply (rule allI)
  apply (erule cd_diff_r)
  done


subsection \<open>pow\<close>

lemma sq_pow_div2 [simp]:
    "m mod 2 = 0 \<Longrightarrow> ((n::nat)*n)^(m div 2) = n^m"
  apply (simp add: power2_eq_square [symmetric] power_mult [symmetric] minus_mod_eq_mult_div [symmetric])
  done

end
