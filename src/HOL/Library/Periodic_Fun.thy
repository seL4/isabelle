(*  Title:    HOL/Library/Periodic_Fun.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Periodic Functions\<close>

theory Periodic_Fun
imports Complex_Main
begin

text \<open>
  A locale for periodic functions. The idea is that one proves $f(x + p) = f(x)$
  for some period $p$ and gets derived results like $f(x - p) = f(x)$ and $f(x + 2p) = f(x)$
  for free.

  @{term g} and @{term gm} are ``plus/minus k periods'' functions. 
  @{term g1} and @{term gn1} are ``plus/minus one period'' functions.
  This is useful e.g. if the period is one; the lemmas one gets are then 
  @{term "f (x + 1) = f x"} instead of @{term "f (x + 1 * 1) = f x"} etc.
\<close>
locale periodic_fun = 
  fixes f :: "('a :: {ring_1}) \<Rightarrow> 'b" and g gm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and g1 gn1 :: "'a \<Rightarrow> 'a"
  assumes plus_1: "f (g1 x) = f x"
  assumes periodic_arg_plus_0: "g x 0 = x"
  assumes periodic_arg_plus_distrib: "g x (of_int (m + n)) = g (g x (of_int n)) (of_int m)"
  assumes plus_1_eq: "g x 1 = g1 x" and minus_1_eq: "g x (-1) = gn1 x" 
          and minus_eq: "g x (-y) = gm x y"
begin

lemma plus_of_nat: "f (g x (of_nat n)) = f x"
  by (induction n) (insert periodic_arg_plus_distrib[of _ 1 "int n" for n], 
                    simp_all add: plus_1 periodic_arg_plus_0 plus_1_eq)

lemma minus_of_nat: "f (gm x (of_nat n)) = f x"
proof -
  have "f (g x (- of_nat n)) = f (g (g x (- of_nat n)) (of_nat n))"
    by (rule plus_of_nat[symmetric])
  also have "\<dots> = f (g (g x (of_int (- of_nat n))) (of_int (of_nat n)))" by simp
  also have "\<dots> = f x" 
    by (subst periodic_arg_plus_distrib [symmetric]) (simp add: periodic_arg_plus_0)
  finally show ?thesis by (simp add: minus_eq)
qed

lemma plus_of_int: "f (g x (of_int n)) = f x"
  by (induction n) (simp_all add: plus_of_nat minus_of_nat minus_eq del: of_nat_Suc)

lemma minus_of_int: "f (gm x (of_int n)) = f x"
  using plus_of_int[of x "of_int (-n)"] by (simp add: minus_eq)

lemma plus_numeral: "f (g x (numeral n)) = f x"
  by (subst of_nat_numeral[symmetric], subst plus_of_nat) (rule refl)

lemma minus_numeral: "f (gm x (numeral n)) = f x"
  by (subst of_nat_numeral[symmetric], subst minus_of_nat) (rule refl)

lemma minus_1: "f (gn1 x) = f x"
  using minus_of_nat[of x 1] by (simp flip: minus_1_eq minus_eq)

lemmas periodic_simps = plus_of_nat minus_of_nat plus_of_int minus_of_int 
                        plus_numeral minus_numeral plus_1 minus_1

end


text \<open>
  Specialised case of the @{term periodic_fun} locale for periods that are not 1.
  Gives lemmas @{term "f (x - period) = f x"} etc.
\<close>
locale periodic_fun_simple = 
  fixes f :: "('a :: {ring_1}) \<Rightarrow> 'b" and period :: 'a
  assumes plus_period: "f (x + period) = f x"
begin
sublocale periodic_fun f "\<lambda>z x. z + x * period" "\<lambda>z x. z - x * period" 
  "\<lambda>z. z + period" "\<lambda>z. z - period"
  by standard (simp_all add: ring_distribs plus_period)
end


text \<open>
  Specialised case of the @{term periodic_fun} locale for period 1.
  Gives lemmas @{term "f (x - 1) = f x"} etc.
\<close>
locale periodic_fun_simple' = 
  fixes f :: "('a :: {ring_1}) \<Rightarrow> 'b"
  assumes plus_period: "f (x + 1) = f x"
begin
sublocale periodic_fun f "\<lambda>z x. z + x" "\<lambda>z x. z - x" "\<lambda>z. z + 1" "\<lambda>z. z - 1"
  by standard (simp_all add: ring_distribs plus_period)

lemma of_nat: "f (of_nat n) = f 0" using plus_of_nat[of 0 n] by simp
lemma uminus_of_nat: "f (-of_nat n) = f 0" using minus_of_nat[of 0 n] by simp
lemma of_int: "f (of_int n) = f 0" using plus_of_int[of 0 n] by simp
lemma uminus_of_int: "f (-of_int n) = f 0" using minus_of_int[of 0 n] by simp
lemma of_numeral: "f (numeral n) = f 0" using plus_numeral[of 0 n] by simp
lemma of_neg_numeral: "f (-numeral n) = f 0" using minus_numeral[of 0 n] by simp
lemma of_1: "f 1 = f 0" using plus_of_nat[of 0 1] by simp
lemma of_neg_1: "f (-1) = f 0" using minus_of_nat[of 0 1] by simp

lemmas periodic_simps' = 
  of_nat uminus_of_nat of_int uminus_of_int of_numeral of_neg_numeral of_1 of_neg_1

end

lemma sin_plus_pi: "sin ((z :: 'a :: {real_normed_field,banach}) + of_real pi) = - sin z"
  by (simp add: sin_add)
  
lemma cos_plus_pi: "cos ((z :: 'a :: {real_normed_field,banach}) + of_real pi) = - cos z"
  by (simp add: cos_add)

interpretation sin: periodic_fun_simple sin "2 * of_real pi :: 'a :: {real_normed_field,banach}"
proof
  fix z :: 'a
  have "sin (z + 2 * of_real pi) = sin (z + of_real pi + of_real pi)" by (simp add: ac_simps)
  also have "\<dots> = sin z" by (simp only: sin_plus_pi) simp
  finally show "sin (z + 2 * of_real pi) = sin z" .
qed

interpretation cos: periodic_fun_simple cos "2 * of_real pi :: 'a :: {real_normed_field,banach}"
proof
  fix z :: 'a
  have "cos (z + 2 * of_real pi) = cos (z + of_real pi + of_real pi)" by (simp add: ac_simps)
  also have "\<dots> = cos z" by (simp only: cos_plus_pi) simp
  finally show "cos (z + 2 * of_real pi) = cos z" .
qed

interpretation tan: periodic_fun_simple tan "2 * of_real pi :: 'a :: {real_normed_field,banach}"
  by standard (simp only: tan_def [abs_def] sin.plus_1 cos.plus_1)

interpretation cot: periodic_fun_simple cot "2 * of_real pi :: 'a :: {real_normed_field,banach}"
  by standard (simp only: cot_def [abs_def] sin.plus_1 cos.plus_1)
  
end
