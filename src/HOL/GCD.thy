(*  Title:      GCD.thy
    Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad, Tobias Nipkow


This file deals with the functions gcd and lcm, and properties of
primes. Definitions and lemmas are proved uniformly for the natural
numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on \cite{davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD". IntPrimes also defined and developed
the congruence relations on the integers. The notion was extended to
the natural numbers by Chiaeb.

Tobias Nipkow cleaned up a lot.
*)


header {* GCD *}

theory GCD
imports NatTransfer
begin

declare One_nat_def [simp del]

subsection {* gcd *}

class gcd = zero + one + dvd +

fixes
  gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and
  lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

begin

abbreviation
  coprime :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "coprime x y == (gcd x y = 1)"

end

class prime = one +

fixes
  prime :: "'a \<Rightarrow> bool"


(* definitions for the natural numbers *)

instantiation nat :: gcd

begin

fun
  gcd_nat  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd_nat x y =
   (if y = 0 then x else gcd y (x mod y))"

definition
  lcm_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "lcm_nat x y = x * y div (gcd x y)"

instance proof qed

end


instantiation nat :: prime

begin

definition
  prime_nat :: "nat \<Rightarrow> bool"
where
  [code del]: "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

instance proof qed

end


(* definitions for the integers *)

instantiation int :: gcd

begin

definition
  gcd_int  :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "gcd_int x y = int (gcd (nat (abs x)) (nat (abs y)))"

definition
  lcm_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "lcm_int x y = int (lcm (nat (abs x)) (nat (abs y)))"

instance proof qed

end


instantiation int :: prime

begin

definition
  prime_int :: "int \<Rightarrow> bool"
where
  [code del]: "prime_int p = prime (nat p)"

instance proof qed

end


subsection {* Set up Transfer *}


lemma transfer_nat_int_gcd:
  "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> gcd (nat x) (nat y) = nat (gcd x y)"
  "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> lcm (nat x) (nat y) = nat (lcm x y)"
  "(x::int) >= 0 \<Longrightarrow> prime (nat x) = prime x"
  unfolding gcd_int_def lcm_int_def prime_int_def
  by auto

lemma transfer_nat_int_gcd_closures:
  "x >= (0::int) \<Longrightarrow> y >= 0 \<Longrightarrow> gcd x y >= 0"
  "x >= (0::int) \<Longrightarrow> y >= 0 \<Longrightarrow> lcm x y >= 0"
  by (auto simp add: gcd_int_def lcm_int_def)

declare TransferMorphism_nat_int[transfer add return:
    transfer_nat_int_gcd transfer_nat_int_gcd_closures]

lemma transfer_int_nat_gcd:
  "gcd (int x) (int y) = int (gcd x y)"
  "lcm (int x) (int y) = int (lcm x y)"
  "prime (int x) = prime x"
  by (unfold gcd_int_def lcm_int_def prime_int_def, auto)

lemma transfer_int_nat_gcd_closures:
  "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> gcd x y >= 0"
  "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> lcm x y >= 0"
  by (auto simp add: gcd_int_def lcm_int_def)

declare TransferMorphism_int_nat[transfer add return:
    transfer_int_nat_gcd transfer_int_nat_gcd_closures]



subsection {* GCD *}

(* was gcd_induct *)
lemma gcd_nat_induct:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
  apply (rule gcd_nat.induct)
  apply (case_tac "y = 0")
  using assms apply simp_all
done

(* specific to int *)

lemma gcd_neg1_int [simp]: "gcd (-x::int) y = gcd x y"
  by (simp add: gcd_int_def)

lemma gcd_neg2_int [simp]: "gcd (x::int) (-y) = gcd x y"
  by (simp add: gcd_int_def)

lemma abs_gcd_int[simp]: "abs(gcd (x::int) y) = gcd x y"
by(simp add: gcd_int_def)

lemma gcd_abs_int: "gcd (x::int) y = gcd (abs x) (abs y)"
by (simp add: gcd_int_def)

lemma gcd_abs1_int[simp]: "gcd (abs x) (y::int) = gcd x y"
by (metis abs_idempotent gcd_abs_int)

lemma gcd_abs2_int[simp]: "gcd x (abs y::int) = gcd x y"
by (metis abs_idempotent gcd_abs_int)

lemma gcd_cases_int:
  fixes x :: int and y
  assumes "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (gcd x y)"
      and "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (gcd x (-y))"
      and "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (gcd (-x) y)"
      and "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (gcd (-x) (-y))"
  shows "P (gcd x y)"
by (insert prems, auto simp add: gcd_neg1_int gcd_neg2_int, arith)

lemma gcd_ge_0_int [simp]: "gcd (x::int) y >= 0"
  by (simp add: gcd_int_def)

lemma lcm_neg1_int: "lcm (-x::int) y = lcm x y"
  by (simp add: lcm_int_def)

lemma lcm_neg2_int: "lcm (x::int) (-y) = lcm x y"
  by (simp add: lcm_int_def)

lemma lcm_abs_int: "lcm (x::int) y = lcm (abs x) (abs y)"
  by (simp add: lcm_int_def)

lemma abs_lcm_int [simp]: "abs (lcm i j::int) = lcm i j"
by(simp add:lcm_int_def)

lemma lcm_abs1_int[simp]: "lcm (abs x) (y::int) = lcm x y"
by (metis abs_idempotent lcm_int_def)

lemma lcm_abs2_int[simp]: "lcm x (abs y::int) = lcm x y"
by (metis abs_idempotent lcm_int_def)

lemma lcm_cases_int:
  fixes x :: int and y
  assumes "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm x y)"
      and "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm x (-y))"
      and "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm (-x) y)"
      and "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm (-x) (-y))"
  shows "P (lcm x y)"
by (insert prems, auto simp add: lcm_neg1_int lcm_neg2_int, arith)

lemma lcm_ge_0_int [simp]: "lcm (x::int) y >= 0"
  by (simp add: lcm_int_def)

(* was gcd_0, etc. *)
lemma gcd_0_nat [simp]: "gcd (x::nat) 0 = x"
  by simp

(* was igcd_0, etc. *)
lemma gcd_0_int [simp]: "gcd (x::int) 0 = abs x"
  by (unfold gcd_int_def, auto)

lemma gcd_0_left_nat [simp]: "gcd 0 (x::nat) = x"
  by simp

lemma gcd_0_left_int [simp]: "gcd 0 (x::int) = abs x"
  by (unfold gcd_int_def, auto)

lemma gcd_red_nat: "gcd (x::nat) y = gcd y (x mod y)"
  by (case_tac "y = 0", auto)

(* weaker, but useful for the simplifier *)

lemma gcd_non_0_nat: "y ~= (0::nat) \<Longrightarrow> gcd (x::nat) y = gcd y (x mod y)"
  by simp

lemma gcd_1_nat [simp]: "gcd (m::nat) 1 = 1"
  by simp

lemma gcd_Suc_0 [simp]: "gcd (m::nat) (Suc 0) = Suc 0"
  by (simp add: One_nat_def)

lemma gcd_1_int [simp]: "gcd (m::int) 1 = 1"
  by (simp add: gcd_int_def)

lemma gcd_idem_nat: "gcd (x::nat) x = x"
by simp

lemma gcd_idem_int: "gcd (x::int) x = abs x"
by (auto simp add: gcd_int_def)

declare gcd_nat.simps [simp del]

text {*
  \medskip @{term "gcd m n"} divides @{text m} and @{text n}.  The
  conjunctions don't seem provable separately.
*}

lemma gcd_dvd1_nat [iff]: "(gcd (m::nat)) n dvd m"
  and gcd_dvd2_nat [iff]: "(gcd m n) dvd n"
  apply (induct m n rule: gcd_nat_induct)
  apply (simp_all add: gcd_non_0_nat)
  apply (blast dest: dvd_mod_imp_dvd)
done

lemma gcd_dvd1_int [iff]: "gcd (x::int) y dvd x"
by (metis gcd_int_def int_dvd_iff gcd_dvd1_nat)

lemma gcd_dvd2_int [iff]: "gcd (x::int) y dvd y"
by (metis gcd_int_def int_dvd_iff gcd_dvd2_nat)

lemma dvd_gcd_D1_nat: "k dvd gcd m n \<Longrightarrow> (k::nat) dvd m"
by(metis gcd_dvd1_nat dvd_trans)

lemma dvd_gcd_D2_nat: "k dvd gcd m n \<Longrightarrow> (k::nat) dvd n"
by(metis gcd_dvd2_nat dvd_trans)

lemma dvd_gcd_D1_int: "i dvd gcd m n \<Longrightarrow> (i::int) dvd m"
by(metis gcd_dvd1_int dvd_trans)

lemma dvd_gcd_D2_int: "i dvd gcd m n \<Longrightarrow> (i::int) dvd n"
by(metis gcd_dvd2_int dvd_trans)

lemma gcd_le1_nat [simp]: "a \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> a"
  by (rule dvd_imp_le, auto)

lemma gcd_le2_nat [simp]: "b \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> b"
  by (rule dvd_imp_le, auto)

lemma gcd_le1_int [simp]: "a > 0 \<Longrightarrow> gcd (a::int) b \<le> a"
  by (rule zdvd_imp_le, auto)

lemma gcd_le2_int [simp]: "b > 0 \<Longrightarrow> gcd (a::int) b \<le> b"
  by (rule zdvd_imp_le, auto)

lemma gcd_greatest_nat: "(k::nat) dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd gcd m n"
by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat dvd_mod)

lemma gcd_greatest_int:
  "(k::int) dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd gcd m n"
  apply (subst gcd_abs_int)
  apply (subst abs_dvd_iff [symmetric])
  apply (rule gcd_greatest_nat [transferred])
  apply auto
done

lemma gcd_greatest_iff_nat [iff]: "(k dvd gcd (m::nat) n) =
    (k dvd m & k dvd n)"
  by (blast intro!: gcd_greatest_nat intro: dvd_trans)

lemma gcd_greatest_iff_int: "((k::int) dvd gcd m n) = (k dvd m & k dvd n)"
  by (blast intro!: gcd_greatest_int intro: dvd_trans)

lemma gcd_zero_nat [simp]: "(gcd (m::nat) n = 0) = (m = 0 & n = 0)"
  by (simp only: dvd_0_left_iff [symmetric] gcd_greatest_iff_nat)

lemma gcd_zero_int [simp]: "(gcd (m::int) n = 0) = (m = 0 & n = 0)"
  by (auto simp add: gcd_int_def)

lemma gcd_pos_nat [simp]: "(gcd (m::nat) n > 0) = (m ~= 0 | n ~= 0)"
  by (insert gcd_zero_nat [of m n], arith)

lemma gcd_pos_int [simp]: "(gcd (m::int) n > 0) = (m ~= 0 | n ~= 0)"
  by (insert gcd_zero_int [of m n], insert gcd_ge_0_int [of m n], arith)

lemma gcd_commute_nat: "gcd (m::nat) n = gcd n m"
  by (rule dvd_anti_sym, auto)

lemma gcd_commute_int: "gcd (m::int) n = gcd n m"
  by (auto simp add: gcd_int_def gcd_commute_nat)

lemma gcd_assoc_nat: "gcd (gcd (k::nat) m) n = gcd k (gcd m n)"
  apply (rule dvd_anti_sym)
  apply (blast intro: dvd_trans)+
done

lemma gcd_assoc_int: "gcd (gcd (k::int) m) n = gcd k (gcd m n)"
  by (auto simp add: gcd_int_def gcd_assoc_nat)

lemmas gcd_left_commute_nat =
  mk_left_commute[of gcd, OF gcd_assoc_nat gcd_commute_nat]

lemmas gcd_left_commute_int =
  mk_left_commute[of gcd, OF gcd_assoc_int gcd_commute_int]

lemmas gcd_ac_nat = gcd_assoc_nat gcd_commute_nat gcd_left_commute_nat
  -- {* gcd is an AC-operator *}

lemmas gcd_ac_int = gcd_assoc_int gcd_commute_int gcd_left_commute_int

lemma gcd_unique_nat: "(d::nat) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  apply auto
  apply (rule dvd_anti_sym)
  apply (erule (1) gcd_greatest_nat)
  apply auto
done

lemma gcd_unique_int: "d >= 0 & (d::int) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  apply (case_tac "d = 0")
  apply force
  apply (rule iffI)
  apply (rule zdvd_anti_sym)
  apply arith
  apply (subst gcd_pos_int)
  apply clarsimp
  apply (drule_tac x = "d + 1" in spec)
  apply (frule zdvd_imp_le)
  apply (auto intro: gcd_greatest_int)
done

lemma gcd_proj1_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> gcd x y = x"
by (metis dvd.eq_iff gcd_unique_nat)

lemma gcd_proj2_if_dvd_nat [simp]: "(y::nat) dvd x \<Longrightarrow> gcd x y = y"
by (metis dvd.eq_iff gcd_unique_nat)

lemma gcd_proj1_if_dvd_int[simp]: "x dvd y \<Longrightarrow> gcd (x::int) y = abs x"
by (metis abs_dvd_iff abs_eq_0 gcd_0_left_int gcd_abs_int gcd_unique_int)

lemma gcd_proj2_if_dvd_int[simp]: "y dvd x \<Longrightarrow> gcd (x::int) y = abs y"
by (metis gcd_proj1_if_dvd_int gcd_commute_int)


text {*
  \medskip Multiplication laws
*}

lemma gcd_mult_distrib_nat: "(k::nat) * gcd m n = gcd (k * m) (k * n)"
    -- {* \cite[page 27]{davenport92} *}
  apply (induct m n rule: gcd_nat_induct)
  apply simp
  apply (case_tac "k = 0")
  apply (simp_all add: mod_geq gcd_non_0_nat mod_mult_distrib2)
done

lemma gcd_mult_distrib_int: "abs (k::int) * gcd m n = gcd (k * m) (k * n)"
  apply (subst (1 2) gcd_abs_int)
  apply (subst (1 2) abs_mult)
  apply (rule gcd_mult_distrib_nat [transferred])
  apply auto
done

lemma coprime_dvd_mult_nat: "coprime (k::nat) n \<Longrightarrow> k dvd m * n \<Longrightarrow> k dvd m"
  apply (insert gcd_mult_distrib_nat [of m k n])
  apply simp
  apply (erule_tac t = m in ssubst)
  apply simp
  done

lemma coprime_dvd_mult_int:
  "coprime (k::int) n \<Longrightarrow> k dvd m * n \<Longrightarrow> k dvd m"
apply (subst abs_dvd_iff [symmetric])
apply (subst dvd_abs_iff [symmetric])
apply (subst (asm) gcd_abs_int)
apply (rule coprime_dvd_mult_nat [transferred])
    prefer 4 apply assumption
   apply auto
apply (subst abs_mult [symmetric], auto)
done

lemma coprime_dvd_mult_iff_nat: "coprime (k::nat) n \<Longrightarrow>
    (k dvd m * n) = (k dvd m)"
  by (auto intro: coprime_dvd_mult_nat)

lemma coprime_dvd_mult_iff_int: "coprime (k::int) n \<Longrightarrow>
    (k dvd m * n) = (k dvd m)"
  by (auto intro: coprime_dvd_mult_int)

lemma gcd_mult_cancel_nat: "coprime k n \<Longrightarrow> gcd ((k::nat) * m) n = gcd m n"
  apply (rule dvd_anti_sym)
  apply (rule gcd_greatest_nat)
  apply (rule_tac n = k in coprime_dvd_mult_nat)
  apply (simp add: gcd_assoc_nat)
  apply (simp add: gcd_commute_nat)
  apply (simp_all add: mult_commute)
done

lemma gcd_mult_cancel_int:
  "coprime (k::int) n \<Longrightarrow> gcd (k * m) n = gcd m n"
apply (subst (1 2) gcd_abs_int)
apply (subst abs_mult)
apply (rule gcd_mult_cancel_nat [transferred], auto)
done

text {* \medskip Addition laws *}

lemma gcd_add1_nat [simp]: "gcd ((m::nat) + n) n = gcd m n"
  apply (case_tac "n = 0")
  apply (simp_all add: gcd_non_0_nat)
done

lemma gcd_add2_nat [simp]: "gcd (m::nat) (m + n) = gcd m n"
  apply (subst (1 2) gcd_commute_nat)
  apply (subst add_commute)
  apply simp
done

(* to do: add the other variations? *)

lemma gcd_diff1_nat: "(m::nat) >= n \<Longrightarrow> gcd (m - n) n = gcd m n"
  by (subst gcd_add1_nat [symmetric], auto)

lemma gcd_diff2_nat: "(n::nat) >= m \<Longrightarrow> gcd (n - m) n = gcd m n"
  apply (subst gcd_commute_nat)
  apply (subst gcd_diff1_nat [symmetric])
  apply auto
  apply (subst gcd_commute_nat)
  apply (subst gcd_diff1_nat)
  apply assumption
  apply (rule gcd_commute_nat)
done

lemma gcd_non_0_int: "(y::int) > 0 \<Longrightarrow> gcd x y = gcd y (x mod y)"
  apply (frule_tac b = y and a = x in pos_mod_sign)
  apply (simp del: pos_mod_sign add: gcd_int_def abs_if nat_mod_distrib)
  apply (auto simp add: gcd_non_0_nat nat_mod_distrib [symmetric]
    zmod_zminus1_eq_if)
  apply (frule_tac a = x in pos_mod_bound)
  apply (subst (1 2) gcd_commute_nat)
  apply (simp del: pos_mod_bound add: nat_diff_distrib gcd_diff2_nat
    nat_le_eq_zle)
done

lemma gcd_red_int: "gcd (x::int) y = gcd y (x mod y)"
  apply (case_tac "y = 0")
  apply force
  apply (case_tac "y > 0")
  apply (subst gcd_non_0_int, auto)
  apply (insert gcd_non_0_int [of "-y" "-x"])
  apply (auto simp add: gcd_neg1_int gcd_neg2_int)
done

lemma gcd_add1_int [simp]: "gcd ((m::int) + n) n = gcd m n"
by (metis gcd_red_int mod_add_self1 zadd_commute)

lemma gcd_add2_int [simp]: "gcd m ((m::int) + n) = gcd m n"
by (metis gcd_add1_int gcd_commute_int zadd_commute)

lemma gcd_add_mult_nat: "gcd (m::nat) (k * m + n) = gcd m n"
by (metis mod_mult_self3 gcd_commute_nat gcd_red_nat)

lemma gcd_add_mult_int: "gcd (m::int) (k * m + n) = gcd m n"
by (metis gcd_commute_int gcd_red_int mod_mult_self1 zadd_commute)


(* to do: differences, and all variations of addition rules
    as simplification rules for nat and int *)

(* FIXME remove iff *)
lemma gcd_dvd_prod_nat [iff]: "gcd (m::nat) n dvd k * n"
  using mult_dvd_mono [of 1] by auto

(* to do: add the three variations of these, and for ints? *)

lemma finite_divisors_nat[simp]:
  assumes "(m::nat) ~= 0" shows "finite{d. d dvd m}"
proof-
  have "finite{d. d <= m}" by(blast intro: bounded_nat_set_is_finite)
  from finite_subset[OF _ this] show ?thesis using assms
    by(bestsimp intro!:dvd_imp_le)
qed

lemma finite_divisors_int[simp]:
  assumes "(i::int) ~= 0" shows "finite{d. d dvd i}"
proof-
  have "{d. abs d <= abs i} = {- abs i .. abs i}" by(auto simp:abs_if)
  hence "finite{d. abs d <= abs i}" by simp
  from finite_subset[OF _ this] show ?thesis using assms
    by(bestsimp intro!:dvd_imp_le_int)
qed

lemma Max_divisors_self_nat[simp]: "n\<noteq>0 \<Longrightarrow> Max{d::nat. d dvd n} = n"
apply(rule antisym)
 apply (fastsimp intro: Max_le_iff[THEN iffD2] simp: dvd_imp_le)
apply simp
done

lemma Max_divisors_self_int[simp]: "n\<noteq>0 \<Longrightarrow> Max{d::int. d dvd n} = abs n"
apply(rule antisym)
 apply(rule Max_le_iff[THEN iffD2])
   apply simp
  apply fastsimp
 apply (metis Collect_def abs_ge_self dvd_imp_le_int mem_def zle_trans)
apply simp
done

lemma gcd_is_Max_divisors_nat:
  "m ~= 0 \<Longrightarrow> n ~= 0 \<Longrightarrow> gcd (m::nat) n = (Max {d. d dvd m & d dvd n})"
apply(rule Max_eqI[THEN sym])
  apply (metis finite_Collect_conjI finite_divisors_nat)
 apply simp
 apply(metis Suc_diff_1 Suc_neq_Zero dvd_imp_le gcd_greatest_iff_nat gcd_pos_nat)
apply simp
done

lemma gcd_is_Max_divisors_int:
  "m ~= 0 ==> n ~= 0 ==> gcd (m::int) n = (Max {d. d dvd m & d dvd n})"
apply(rule Max_eqI[THEN sym])
  apply (metis finite_Collect_conjI finite_divisors_int)
 apply simp
 apply (metis gcd_greatest_iff_int gcd_pos_int zdvd_imp_le)
apply simp
done


subsection {* Coprimality *}

lemma div_gcd_coprime_nat:
  assumes nz: "(a::nat) \<noteq> 0 \<or> b \<noteq> 0"
  shows "coprime (a div gcd a b) (b div gcd a b)"
proof -
  let ?g = "gcd a b"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "gcd ?a' ?b'"
  have dvdg: "?g dvd a" "?g dvd b" by simp_all
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'" by simp_all
  from dvdg dvdg' obtain ka kb ka' kb' where
      kab: "a = ?g * ka" "b = ?g * kb" "?a' = ?g' * ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  then have "?g * ?a' = (?g * ?g') * ka'" "?g * ?b' = (?g * ?g') * kb'"
    by simp_all
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp add: dvd_mult_div_cancel [OF dvdg(1)]
      dvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0" using nz by (simp add: gcd_zero_nat)
  then have gp: "?g > 0" by arith
  from gcd_greatest_nat [OF dvdgg'] have "?g * ?g' dvd ?g" .
  with dvd_mult_cancel1 [OF gp] show "?g' = 1" by simp
qed

lemma div_gcd_coprime_int:
  assumes nz: "(a::int) \<noteq> 0 \<or> b \<noteq> 0"
  shows "coprime (a div gcd a b) (b div gcd a b)"
apply (subst (1 2 3) gcd_abs_int)
apply (subst (1 2) abs_div)
  apply simp
 apply simp
apply(subst (1 2) abs_gcd_int)
apply (rule div_gcd_coprime_nat [transferred])
using nz apply (auto simp add: gcd_abs_int [symmetric])
done

lemma coprime_nat: "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using gcd_unique_nat[of 1 a b, simplified] by auto

lemma coprime_Suc_0_nat:
    "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = Suc 0)"
  using coprime_nat by (simp add: One_nat_def)

lemma coprime_int: "coprime (a::int) b \<longleftrightarrow>
    (\<forall>d. d >= 0 \<and> d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using gcd_unique_int [of 1 a b]
  apply clarsimp
  apply (erule subst)
  apply (rule iffI)
  apply force
  apply (drule_tac x = "abs e" in exI)
  apply (case_tac "e >= 0")
  apply force
  apply force
done

lemma gcd_coprime_nat:
  assumes z: "gcd (a::nat) b \<noteq> 0" and a: "a = a' * gcd a b" and
    b: "b = b' * gcd a b"
  shows    "coprime a' b'"

  apply (subgoal_tac "a' = a div gcd a b")
  apply (erule ssubst)
  apply (subgoal_tac "b' = b div gcd a b")
  apply (erule ssubst)
  apply (rule div_gcd_coprime_nat)
  using prems
  apply force
  apply (subst (1) b)
  using z apply force
  apply (subst (1) a)
  using z apply force
done

lemma gcd_coprime_int:
  assumes z: "gcd (a::int) b \<noteq> 0" and a: "a = a' * gcd a b" and
    b: "b = b' * gcd a b"
  shows    "coprime a' b'"

  apply (subgoal_tac "a' = a div gcd a b")
  apply (erule ssubst)
  apply (subgoal_tac "b' = b div gcd a b")
  apply (erule ssubst)
  apply (rule div_gcd_coprime_int)
  using prems
  apply force
  apply (subst (1) b)
  using z apply force
  apply (subst (1) a)
  using z apply force
done

lemma coprime_mult_nat: assumes da: "coprime (d::nat) a" and db: "coprime d b"
    shows "coprime d (a * b)"
  apply (subst gcd_commute_nat)
  using da apply (subst gcd_mult_cancel_nat)
  apply (subst gcd_commute_nat, assumption)
  apply (subst gcd_commute_nat, rule db)
done

lemma coprime_mult_int: assumes da: "coprime (d::int) a" and db: "coprime d b"
    shows "coprime d (a * b)"
  apply (subst gcd_commute_int)
  using da apply (subst gcd_mult_cancel_int)
  apply (subst gcd_commute_int, assumption)
  apply (subst gcd_commute_int, rule db)
done

lemma coprime_lmult_nat:
  assumes dab: "coprime (d::nat) (a * b)" shows "coprime d a"
proof -
  have "gcd d a dvd gcd d (a * b)"
    by (rule gcd_greatest_nat, auto)
  with dab show ?thesis
    by auto
qed

lemma coprime_lmult_int:
  assumes "coprime (d::int) (a * b)" shows "coprime d a"
proof -
  have "gcd d a dvd gcd d (a * b)"
    by (rule gcd_greatest_int, auto)
  with assms show ?thesis
    by auto
qed

lemma coprime_rmult_nat:
  assumes "coprime (d::nat) (a * b)" shows "coprime d b"
proof -
  have "gcd d b dvd gcd d (a * b)"
    by (rule gcd_greatest_nat, auto intro: dvd_mult)
  with assms show ?thesis
    by auto
qed

lemma coprime_rmult_int:
  assumes dab: "coprime (d::int) (a * b)" shows "coprime d b"
proof -
  have "gcd d b dvd gcd d (a * b)"
    by (rule gcd_greatest_int, auto intro: dvd_mult)
  with dab show ?thesis
    by auto
qed

lemma coprime_mul_eq_nat: "coprime (d::nat) (a * b) \<longleftrightarrow>
    coprime d a \<and>  coprime d b"
  using coprime_rmult_nat[of d a b] coprime_lmult_nat[of d a b]
    coprime_mult_nat[of d a b]
  by blast

lemma coprime_mul_eq_int: "coprime (d::int) (a * b) \<longleftrightarrow>
    coprime d a \<and>  coprime d b"
  using coprime_rmult_int[of d a b] coprime_lmult_int[of d a b]
    coprime_mult_int[of d a b]
  by blast

lemma gcd_coprime_exists_nat:
    assumes nz: "gcd (a::nat) b \<noteq> 0"
    shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
  apply (rule_tac x = "a div gcd a b" in exI)
  apply (rule_tac x = "b div gcd a b" in exI)
  using nz apply (auto simp add: div_gcd_coprime_nat dvd_div_mult)
done

lemma gcd_coprime_exists_int:
    assumes nz: "gcd (a::int) b \<noteq> 0"
    shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
  apply (rule_tac x = "a div gcd a b" in exI)
  apply (rule_tac x = "b div gcd a b" in exI)
  using nz apply (auto simp add: div_gcd_coprime_int dvd_div_mult_self)
done

lemma coprime_exp_nat: "coprime (d::nat) a \<Longrightarrow> coprime d (a^n)"
  by (induct n, simp_all add: coprime_mult_nat)

lemma coprime_exp_int: "coprime (d::int) a \<Longrightarrow> coprime d (a^n)"
  by (induct n, simp_all add: coprime_mult_int)

lemma coprime_exp2_nat [intro]: "coprime (a::nat) b \<Longrightarrow> coprime (a^n) (b^m)"
  apply (rule coprime_exp_nat)
  apply (subst gcd_commute_nat)
  apply (rule coprime_exp_nat)
  apply (subst gcd_commute_nat, assumption)
done

lemma coprime_exp2_int [intro]: "coprime (a::int) b \<Longrightarrow> coprime (a^n) (b^m)"
  apply (rule coprime_exp_int)
  apply (subst gcd_commute_int)
  apply (rule coprime_exp_int)
  apply (subst gcd_commute_int, assumption)
done

lemma gcd_exp_nat: "gcd ((a::nat)^n) (b^n) = (gcd a b)^n"
proof (cases)
  assume "a = 0 & b = 0"
  thus ?thesis by simp
  next assume "~(a = 0 & b = 0)"
  hence "coprime ((a div gcd a b)^n) ((b div gcd a b)^n)"
    by (auto simp:div_gcd_coprime_nat)
  hence "gcd ((a div gcd a b)^n * (gcd a b)^n)
      ((b div gcd a b)^n * (gcd a b)^n) = (gcd a b)^n"
    apply (subst (1 2) mult_commute)
    apply (subst gcd_mult_distrib_nat [symmetric])
    apply simp
    done
  also have "(a div gcd a b)^n * (gcd a b)^n = a^n"
    apply (subst div_power)
    apply auto
    apply (rule dvd_div_mult_self)
    apply (rule dvd_power_same)
    apply auto
    done
  also have "(b div gcd a b)^n * (gcd a b)^n = b^n"
    apply (subst div_power)
    apply auto
    apply (rule dvd_div_mult_self)
    apply (rule dvd_power_same)
    apply auto
    done
  finally show ?thesis .
qed

lemma gcd_exp_int: "gcd ((a::int)^n) (b^n) = (gcd a b)^n"
  apply (subst (1 2) gcd_abs_int)
  apply (subst (1 2) power_abs)
  apply (rule gcd_exp_nat [where n = n, transferred])
  apply auto
done

lemma coprime_divprod_nat: "(d::nat) dvd a * b  \<Longrightarrow> coprime d a \<Longrightarrow> d dvd b"
  using coprime_dvd_mult_iff_nat[of d a b]
  by (auto simp add: mult_commute)

lemma coprime_divprod_int: "(d::int) dvd a * b  \<Longrightarrow> coprime d a \<Longrightarrow> d dvd b"
  using coprime_dvd_mult_iff_int[of d a b]
  by (auto simp add: mult_commute)

lemma division_decomp_nat: assumes dc: "(a::nat) dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof-
  let ?g = "gcd a b"
  {assume "?g = 0" with dc have ?thesis by auto}
  moreover
  {assume z: "?g \<noteq> 0"
    from gcd_coprime_exists_nat[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
      by blast
    have thb: "?g dvd b" by auto
    from ab'(1) have "a' dvd a"  unfolding dvd_def by blast
    with dc have th0: "a' dvd b*c" using dvd_trans[of a' a "b*c"] by simp
    from dc ab'(1,2) have "a'*?g dvd (b'*?g) *c" by auto
    hence "?g*a' dvd ?g * (b' * c)" by (simp add: mult_assoc)
    with z have th_1: "a' dvd b' * c" by auto
    from coprime_dvd_mult_nat[OF ab'(3)] th_1
    have thc: "a' dvd c" by (subst (asm) mult_commute, blast)
    from ab' have "a = ?g*a'" by algebra
    with thb thc have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma division_decomp_int: assumes dc: "(a::int) dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof-
  let ?g = "gcd a b"
  {assume "?g = 0" with dc have ?thesis by auto}
  moreover
  {assume z: "?g \<noteq> 0"
    from gcd_coprime_exists_int[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
      by blast
    have thb: "?g dvd b" by auto
    from ab'(1) have "a' dvd a"  unfolding dvd_def by blast
    with dc have th0: "a' dvd b*c"
      using dvd_trans[of a' a "b*c"] by simp
    from dc ab'(1,2) have "a'*?g dvd (b'*?g) *c" by auto
    hence "?g*a' dvd ?g * (b' * c)" by (simp add: mult_assoc)
    with z have th_1: "a' dvd b' * c" by auto
    from coprime_dvd_mult_int[OF ab'(3)] th_1
    have thc: "a' dvd c" by (subst (asm) mult_commute, blast)
    from ab' have "a = ?g*a'" by algebra
    with thb thc have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma pow_divides_pow_nat:
  assumes ab: "(a::nat) ^ n dvd b ^n" and n:"n \<noteq> 0"
  shows "a dvd b"
proof-
  let ?g = "gcd a b"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  {assume "?g = 0" with ab n have ?thesis by auto }
  moreover
  {assume z: "?g \<noteq> 0"
    hence zn: "?g ^ n \<noteq> 0" using n by (simp add: neq0_conv)
    from gcd_coprime_exists_nat[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
      by blast
    from ab have "(a' * ?g) ^ n dvd (b' * ?g)^n"
      by (simp add: ab'(1,2)[symmetric])
    hence "?g^n*a'^n dvd ?g^n *b'^n"
      by (simp only: power_mult_distrib mult_commute)
    with zn z n have th0:"a'^n dvd b'^n" by auto
    have "a' dvd a'^n" by (simp add: m)
    with th0 have "a' dvd b'^n" using dvd_trans[of a' "a'^n" "b'^n"] by simp
    hence th1: "a' dvd b'^m * b'" by (simp add: m mult_commute)
    from coprime_dvd_mult_nat[OF coprime_exp_nat [OF ab'(3), of m]] th1
    have "a' dvd b'" by (subst (asm) mult_commute, blast)
    hence "a'*?g dvd b'*?g" by simp
    with ab'(1,2)  have ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma pow_divides_pow_int:
  assumes ab: "(a::int) ^ n dvd b ^n" and n:"n \<noteq> 0"
  shows "a dvd b"
proof-
  let ?g = "gcd a b"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  {assume "?g = 0" with ab n have ?thesis by auto }
  moreover
  {assume z: "?g \<noteq> 0"
    hence zn: "?g ^ n \<noteq> 0" using n by (simp add: neq0_conv)
    from gcd_coprime_exists_int[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
      by blast
    from ab have "(a' * ?g) ^ n dvd (b' * ?g)^n"
      by (simp add: ab'(1,2)[symmetric])
    hence "?g^n*a'^n dvd ?g^n *b'^n"
      by (simp only: power_mult_distrib mult_commute)
    with zn z n have th0:"a'^n dvd b'^n" by auto
    have "a' dvd a'^n" by (simp add: m)
    with th0 have "a' dvd b'^n"
      using dvd_trans[of a' "a'^n" "b'^n"] by simp
    hence th1: "a' dvd b'^m * b'" by (simp add: m mult_commute)
    from coprime_dvd_mult_int[OF coprime_exp_int [OF ab'(3), of m]] th1
    have "a' dvd b'" by (subst (asm) mult_commute, blast)
    hence "a'*?g dvd b'*?g" by simp
    with ab'(1,2)  have ?thesis by simp }
  ultimately show ?thesis by blast
qed

(* FIXME move to Divides(?) *)
lemma pow_divides_eq_nat [simp]: "n ~= 0 \<Longrightarrow> ((a::nat)^n dvd b^n) = (a dvd b)"
  by (auto intro: pow_divides_pow_nat dvd_power_same)

lemma pow_divides_eq_int [simp]: "n ~= 0 \<Longrightarrow> ((a::int)^n dvd b^n) = (a dvd b)"
  by (auto intro: pow_divides_pow_int dvd_power_same)

lemma divides_mult_nat:
  assumes mr: "(m::nat) dvd r" and nr: "n dvd r" and mn:"coprime m n"
  shows "m * n dvd r"
proof-
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: mult_commute)
  hence "m dvd n'" using coprime_dvd_mult_iff_nat[OF mn] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  from n' k show ?thesis unfolding dvd_def by auto
qed

lemma divides_mult_int:
  assumes mr: "(m::int) dvd r" and nr: "n dvd r" and mn:"coprime m n"
  shows "m * n dvd r"
proof-
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: mult_commute)
  hence "m dvd n'" using coprime_dvd_mult_iff_int[OF mn] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  from n' k show ?thesis unfolding dvd_def by auto
qed

lemma coprime_plus_one_nat [simp]: "coprime ((n::nat) + 1) n"
  apply (subgoal_tac "gcd (n + 1) n dvd (n + 1 - n)")
  apply force
  apply (rule dvd_diff_nat)
  apply auto
done

lemma coprime_Suc_nat [simp]: "coprime (Suc n) n"
  using coprime_plus_one_nat by (simp add: One_nat_def)

lemma coprime_plus_one_int [simp]: "coprime ((n::int) + 1) n"
  apply (subgoal_tac "gcd (n + 1) n dvd (n + 1 - n)")
  apply force
  apply (rule dvd_diff)
  apply auto
done

lemma coprime_minus_one_nat: "(n::nat) \<noteq> 0 \<Longrightarrow> coprime (n - 1) n"
  using coprime_plus_one_nat [of "n - 1"]
    gcd_commute_nat [of "n - 1" n] by auto

lemma coprime_minus_one_int: "coprime ((n::int) - 1) n"
  using coprime_plus_one_int [of "n - 1"]
    gcd_commute_int [of "n - 1" n] by auto

lemma setprod_coprime_nat [rule_format]:
    "(ALL i: A. coprime (f i) (x::nat)) --> coprime (PROD i:A. f i) x"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto simp add: gcd_mult_cancel_nat)
done

lemma setprod_coprime_int [rule_format]:
    "(ALL i: A. coprime (f i) (x::int)) --> coprime (PROD i:A. f i) x"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto simp add: gcd_mult_cancel_int)
done

lemma prime_odd_nat: "prime (p::nat) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  unfolding prime_nat_def
  apply (subst even_mult_two_ex)
  apply clarify
  apply (drule_tac x = 2 in spec)
  apply auto
done

lemma prime_odd_int: "prime (p::int) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  unfolding prime_int_def
  apply (frule prime_odd_nat)
  apply (auto simp add: even_nat_def)
done

lemma coprime_common_divisor_nat: "coprime (a::nat) b \<Longrightarrow> x dvd a \<Longrightarrow>
    x dvd b \<Longrightarrow> x = 1"
  apply (subgoal_tac "x dvd gcd a b")
  apply simp
  apply (erule (1) gcd_greatest_nat)
done

lemma coprime_common_divisor_int: "coprime (a::int) b \<Longrightarrow> x dvd a \<Longrightarrow>
    x dvd b \<Longrightarrow> abs x = 1"
  apply (subgoal_tac "x dvd gcd a b")
  apply simp
  apply (erule (1) gcd_greatest_int)
done

lemma coprime_divisors_nat: "(d::int) dvd a \<Longrightarrow> e dvd b \<Longrightarrow> coprime a b \<Longrightarrow>
    coprime d e"
  apply (auto simp add: dvd_def)
  apply (frule coprime_lmult_int)
  apply (subst gcd_commute_int)
  apply (subst (asm) (2) gcd_commute_int)
  apply (erule coprime_lmult_int)
done

lemma invertible_coprime_nat: "(x::nat) * y mod m = 1 \<Longrightarrow> coprime x m"
apply (metis coprime_lmult_nat gcd_1_nat gcd_commute_nat gcd_red_nat)
done

lemma invertible_coprime_int: "(x::int) * y mod m = 1 \<Longrightarrow> coprime x m"
apply (metis coprime_lmult_int gcd_1_int gcd_commute_int gcd_red_int)
done


subsection {* Bezout's theorem *}

(* Function bezw returns a pair of witnesses to Bezout's theorem --
   see the theorems that follow the definition. *)
fun
  bezw  :: "nat \<Rightarrow> nat \<Rightarrow> int * int"
where
  "bezw x y =
  (if y = 0 then (1, 0) else
      (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y)))"

lemma bezw_0 [simp]: "bezw x 0 = (1, 0)" by simp

lemma bezw_non_0: "y > 0 \<Longrightarrow> bezw x y = (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y))"
  by simp

declare bezw.simps [simp del]

lemma bezw_aux [rule_format]:
    "fst (bezw x y) * int x + snd (bezw x y) * int y = int (gcd x y)"
proof (induct x y rule: gcd_nat_induct)
  fix m :: nat
  show "fst (bezw m 0) * int m + snd (bezw m 0) * int 0 = int (gcd m 0)"
    by auto
  next fix m :: nat and n
    assume ngt0: "n > 0" and
      ih: "fst (bezw n (m mod n)) * int n +
        snd (bezw n (m mod n)) * int (m mod n) =
        int (gcd n (m mod n))"
    thus "fst (bezw m n) * int m + snd (bezw m n) * int n = int (gcd m n)"
      apply (simp add: bezw_non_0 gcd_non_0_nat)
      apply (erule subst)
      apply (simp add: ring_simps)
      apply (subst mod_div_equality [of m n, symmetric])
      (* applying simp here undoes the last substitution!
         what is procedure cancel_div_mod? *)
      apply (simp only: ring_simps zadd_int [symmetric]
        zmult_int [symmetric])
      done
qed

lemma bezout_int:
  fixes x y
  shows "EX u v. u * (x::int) + v * y = gcd x y"
proof -
  have bezout_aux: "!!x y. x \<ge> (0::int) \<Longrightarrow> y \<ge> 0 \<Longrightarrow>
      EX u v. u * x + v * y = gcd x y"
    apply (rule_tac x = "fst (bezw (nat x) (nat y))" in exI)
    apply (rule_tac x = "snd (bezw (nat x) (nat y))" in exI)
    apply (unfold gcd_int_def)
    apply simp
    apply (subst bezw_aux [symmetric])
    apply auto
    done
  have "(x \<ge> 0 \<and> y \<ge> 0) | (x \<ge> 0 \<and> y \<le> 0) | (x \<le> 0 \<and> y \<ge> 0) |
      (x \<le> 0 \<and> y \<le> 0)"
    by auto
  moreover have "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    by (erule (1) bezout_aux)
  moreover have "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of x "-y"])
    apply auto
    apply (rule_tac x = u in exI)
    apply (rule_tac x = "-v" in exI)
    apply (subst gcd_neg2_int [symmetric])
    apply auto
    done
  moreover have "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of "-x" y])
    apply auto
    apply (rule_tac x = "-u" in exI)
    apply (rule_tac x = v in exI)
    apply (subst gcd_neg1_int [symmetric])
    apply auto
    done
  moreover have "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of "-x" "-y"])
    apply auto
    apply (rule_tac x = "-u" in exI)
    apply (rule_tac x = "-v" in exI)
    apply (subst gcd_neg1_int [symmetric])
    apply (subst gcd_neg2_int [symmetric])
    apply auto
    done
  ultimately show ?thesis by blast
qed

text {* versions of Bezout for nat, by Amine Chaieb *}

lemma ind_euclid:
  assumes c: " \<forall>a b. P (a::nat) b \<longleftrightarrow> P b a" and z: "\<forall>a. P a 0"
  and add: "\<forall>a b. P a b \<longrightarrow> P a (a + b)"
  shows "P a b"
proof(induct n\<equiv>"a+b" arbitrary: a b rule: nat_less_induct)
  fix n a b
  assume H: "\<forall>m < n. \<forall>a b. m = a + b \<longrightarrow> P a b" "n = a + b"
  have "a = b \<or> a < b \<or> b < a" by arith
  moreover {assume eq: "a= b"
    from add[rule_format, OF z[rule_format, of a]] have "P a b" using eq
    by simp}
  moreover
  {assume lt: "a < b"
    hence "a + b - a < n \<or> a = 0"  using H(2) by arith
    moreover
    {assume "a =0" with z c have "P a b" by blast }
    moreover
    {assume ab: "a + b - a < n"
      have th0: "a + b - a = a + (b - a)" using lt by arith
      from add[rule_format, OF H(1)[rule_format, OF ab th0]]
      have "P a b" by (simp add: th0[symmetric])}
    ultimately have "P a b" by blast}
  moreover
  {assume lt: "a > b"
    hence "b + a - b < n \<or> b = 0"  using H(2) by arith
    moreover
    {assume "b =0" with z c have "P a b" by blast }
    moreover
    {assume ab: "b + a - b < n"
      have th0: "b + a - b = b + (a - b)" using lt by arith
      from add[rule_format, OF H(1)[rule_format, OF ab th0]]
      have "P b a" by (simp add: th0[symmetric])
      hence "P a b" using c by blast }
    ultimately have "P a b" by blast}
ultimately  show "P a b" by blast
qed

lemma bezout_lemma_nat:
  assumes ex: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x = b * y + d \<or> b * x = a * y + d)"
  shows "\<exists>d x y. d dvd a \<and> d dvd a + b \<and>
    (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
  using ex
  apply clarsimp
  apply (rule_tac x="d" in exI, simp add: dvd_add)
  apply (case_tac "a * x = b * y + d" , simp_all)
  apply (rule_tac x="x + y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x + y" in exI)
  apply algebra
done

lemma bezout_add_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x = b * y + d \<or> b * x = a * y + d)"
  apply(induct a b rule: ind_euclid)
  apply blast
  apply clarify
  apply (rule_tac x="a" in exI, simp add: dvd_add)
  apply clarsimp
  apply (rule_tac x="d" in exI)
  apply (case_tac "a * x = b * y + d", simp_all add: dvd_add)
  apply (rule_tac x="x+y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x+y" in exI)
  apply algebra
done

lemma bezout1_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x - b * y = d \<or> b * x - a * y = d)"
  using bezout_add_nat[of a b]
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="y" in exI)
  apply auto
done

lemma bezout_add_strong_nat: assumes nz: "a \<noteq> (0::nat)"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
proof-
 from nz have ap: "a > 0" by simp
 from bezout_add_nat[of a b]
 have "(\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d) \<or>
   (\<exists>d x y. d dvd a \<and> d dvd b \<and> b * x = a * y + d)" by blast
 moreover
    {fix d x y assume H: "d dvd a" "d dvd b" "a * x = b * y + d"
     from H have ?thesis by blast }
 moreover
 {fix d x y assume H: "d dvd a" "d dvd b" "b * x = a * y + d"
   {assume b0: "b = 0" with H  have ?thesis by simp}
   moreover
   {assume b: "b \<noteq> 0" hence bp: "b > 0" by simp
     from b dvd_imp_le [OF H(2)] have "d < b \<or> d = b"
       by auto
     moreover
     {assume db: "d=b"
       from prems have ?thesis apply simp
	 apply (rule exI[where x = b], simp)
	 apply (rule exI[where x = b])
	by (rule exI[where x = "a - 1"], simp add: diff_mult_distrib2)}
    moreover
    {assume db: "d < b"
	{assume "x=0" hence ?thesis  using prems by simp }
	moreover
	{assume x0: "x \<noteq> 0" hence xp: "x > 0" by simp
	  from db have "d \<le> b - 1" by simp
	  hence "d*b \<le> b*(b - 1)" by simp
	  with xp mult_mono[of "1" "x" "d*b" "b*(b - 1)"]
	  have dble: "d*b \<le> x*b*(b - 1)" using bp by simp
	  from H (3) have "d + (b - 1) * (b*x) = d + (b - 1) * (a*y + d)"
            by simp
	  hence "d + (b - 1) * a * y + (b - 1) * d = d + (b - 1) * b * x"
	    by (simp only: mult_assoc right_distrib)
	  hence "a * ((b - 1) * y) + d * (b - 1 + 1) = d + x*b*(b - 1)"
            by algebra
	  hence "a * ((b - 1) * y) = d + x*b*(b - 1) - d*b" using bp by simp
	  hence "a * ((b - 1) * y) = d + (x*b*(b - 1) - d*b)"
	    by (simp only: diff_add_assoc[OF dble, of d, symmetric])
	  hence "a * ((b - 1) * y) = b*(x*(b - 1) - d) + d"
	    by (simp only: diff_mult_distrib2 add_commute mult_ac)
	  hence ?thesis using H(1,2)
	    apply -
	    apply (rule exI[where x=d], simp)
	    apply (rule exI[where x="(b - 1) * y"])
	    by (rule exI[where x="x*(b - 1) - d"], simp)}
	ultimately have ?thesis by blast}
    ultimately have ?thesis by blast}
  ultimately have ?thesis by blast}
 ultimately show ?thesis by blast
qed

lemma bezout_nat: assumes a: "(a::nat) \<noteq> 0"
  shows "\<exists>x y. a * x = b * y + gcd a b"
proof-
  let ?g = "gcd a b"
  from bezout_add_strong_nat[OF a, of b]
  obtain d x y where d: "d dvd a" "d dvd b" "a * x = b * y + d" by blast
  from d(1,2) have "d dvd ?g" by simp
  then obtain k where k: "?g = d*k" unfolding dvd_def by blast
  from d(3) have "a * x * k = (b * y + d) *k " by auto
  hence "a * (x * k) = b * (y*k) + ?g" by (algebra add: k)
  thus ?thesis by blast
qed


subsection {* LCM *}

lemma lcm_altdef_int: "lcm (a::int) b = (abs a) * (abs b) div gcd a b"
  by (simp add: lcm_int_def lcm_nat_def zdiv_int
    zmult_int [symmetric] gcd_int_def)

lemma prod_gcd_lcm_nat: "(m::nat) * n = gcd m n * lcm m n"
  unfolding lcm_nat_def
  by (simp add: dvd_mult_div_cancel [OF gcd_dvd_prod_nat])

lemma prod_gcd_lcm_int: "abs(m::int) * abs n = gcd m n * lcm m n"
  unfolding lcm_int_def gcd_int_def
  apply (subst int_mult [symmetric])
  apply (subst prod_gcd_lcm_nat [symmetric])
  apply (subst nat_abs_mult_distrib [symmetric])
  apply (simp, simp add: abs_mult)
done

lemma lcm_0_nat [simp]: "lcm (m::nat) 0 = 0"
  unfolding lcm_nat_def by simp

lemma lcm_0_int [simp]: "lcm (m::int) 0 = 0"
  unfolding lcm_int_def by simp

lemma lcm_0_left_nat [simp]: "lcm (0::nat) n = 0"
  unfolding lcm_nat_def by simp

lemma lcm_0_left_int [simp]: "lcm (0::int) n = 0"
  unfolding lcm_int_def by simp

lemma lcm_commute_nat: "lcm (m::nat) n = lcm n m"
  unfolding lcm_nat_def by (simp add: gcd_commute_nat ring_simps)

lemma lcm_commute_int: "lcm (m::int) n = lcm n m"
  unfolding lcm_int_def by (subst lcm_commute_nat, rule refl)


lemma lcm_pos_nat:
  "(m::nat) > 0 \<Longrightarrow> n>0 \<Longrightarrow> lcm m n > 0"
by (metis gr0I mult_is_0 prod_gcd_lcm_nat)

lemma lcm_pos_int:
  "(m::int) ~= 0 \<Longrightarrow> n ~= 0 \<Longrightarrow> lcm m n > 0"
  apply (subst lcm_abs_int)
  apply (rule lcm_pos_nat [transferred])
  apply auto
done

lemma dvd_pos_nat:
  fixes n m :: nat
  assumes "n > 0" and "m dvd n"
  shows "m > 0"
using assms by (cases m) auto

lemma lcm_least_nat:
  assumes "(m::nat) dvd k" and "n dvd k"
  shows "lcm m n dvd k"
proof (cases k)
  case 0 then show ?thesis by auto
next
  case (Suc _) then have pos_k: "k > 0" by auto
  from assms dvd_pos_nat [OF this] have pos_mn: "m > 0" "n > 0" by auto
  with gcd_zero_nat [of m n] have pos_gcd: "gcd m n > 0" by simp
  from assms obtain p where k_m: "k = m * p" using dvd_def by blast
  from assms obtain q where k_n: "k = n * q" using dvd_def by blast
  from pos_k k_m have pos_p: "p > 0" by auto
  from pos_k k_n have pos_q: "q > 0" by auto
  have "k * k * gcd q p = k * gcd (k * q) (k * p)"
    by (simp add: mult_ac gcd_mult_distrib_nat)
  also have "\<dots> = k * gcd (m * p * q) (n * q * p)"
    by (simp add: k_m [symmetric] k_n [symmetric])
  also have "\<dots> = k * p * q * gcd m n"
    by (simp add: mult_ac gcd_mult_distrib_nat)
  finally have "(m * p) * (n * q) * gcd q p = k * p * q * gcd m n"
    by (simp only: k_m [symmetric] k_n [symmetric])
  then have "p * q * m * n * gcd q p = p * q * k * gcd m n"
    by (simp add: mult_ac)
  with pos_p pos_q have "m * n * gcd q p = k * gcd m n"
    by simp
  with prod_gcd_lcm_nat [of m n]
  have "lcm m n * gcd q p * gcd m n = k * gcd m n"
    by (simp add: mult_ac)
  with pos_gcd have "lcm m n * gcd q p = k" by auto
  then show ?thesis using dvd_def by auto
qed

lemma lcm_least_int:
  "(m::int) dvd k \<Longrightarrow> n dvd k \<Longrightarrow> lcm m n dvd k"
apply (subst lcm_abs_int)
apply (rule dvd_trans)
apply (rule lcm_least_nat [transferred, of _ "abs k" _])
apply auto
done

lemma lcm_dvd1_nat: "(m::nat) dvd lcm m n"
proof (cases m)
  case 0 then show ?thesis by simp
next
  case (Suc _)
  then have mpos: "m > 0" by simp
  show ?thesis
  proof (cases n)
    case 0 then show ?thesis by simp
  next
    case (Suc _)
    then have npos: "n > 0" by simp
    have "gcd m n dvd n" by simp
    then obtain k where "n = gcd m n * k" using dvd_def by auto
    then have "m * n div gcd m n = m * (gcd m n * k) div gcd m n"
      by (simp add: mult_ac)
    also have "\<dots> = m * k" using mpos npos gcd_zero_nat by simp
    finally show ?thesis by (simp add: lcm_nat_def)
  qed
qed

lemma lcm_dvd1_int: "(m::int) dvd lcm m n"
  apply (subst lcm_abs_int)
  apply (rule dvd_trans)
  prefer 2
  apply (rule lcm_dvd1_nat [transferred])
  apply auto
done

lemma lcm_dvd2_nat: "(n::nat) dvd lcm m n"
  by (subst lcm_commute_nat, rule lcm_dvd1_nat)

lemma lcm_dvd2_int: "(n::int) dvd lcm m n"
  by (subst lcm_commute_int, rule lcm_dvd1_int)

lemma dvd_lcm_I1_nat[simp]: "(k::nat) dvd m \<Longrightarrow> k dvd lcm m n"
by(metis lcm_dvd1_nat dvd_trans)

lemma dvd_lcm_I2_nat[simp]: "(k::nat) dvd n \<Longrightarrow> k dvd lcm m n"
by(metis lcm_dvd2_nat dvd_trans)

lemma dvd_lcm_I1_int[simp]: "(i::int) dvd m \<Longrightarrow> i dvd lcm m n"
by(metis lcm_dvd1_int dvd_trans)

lemma dvd_lcm_I2_int[simp]: "(i::int) dvd n \<Longrightarrow> i dvd lcm m n"
by(metis lcm_dvd2_int dvd_trans)

lemma lcm_unique_nat: "(a::nat) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (auto intro: dvd_anti_sym lcm_least_nat lcm_dvd1_nat lcm_dvd2_nat)

lemma lcm_unique_int: "d >= 0 \<and> (a::int) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (auto intro: dvd_anti_sym [transferred] lcm_least_int)

lemma lcm_proj2_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> lcm x y = y"
  apply (rule sym)
  apply (subst lcm_unique_nat [symmetric])
  apply auto
done

lemma lcm_proj2_if_dvd_int [simp]: "(x::int) dvd y \<Longrightarrow> lcm x y = abs y"
  apply (rule sym)
  apply (subst lcm_unique_int [symmetric])
  apply auto
done

lemma lcm_proj1_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> lcm y x = y"
by (subst lcm_commute_nat, erule lcm_proj2_if_dvd_nat)

lemma lcm_proj1_if_dvd_int [simp]: "(x::int) dvd y \<Longrightarrow> lcm y x = abs y"
by (subst lcm_commute_int, erule lcm_proj2_if_dvd_int)

lemma lcm_proj1_iff_nat[simp]: "lcm m n = (m::nat) \<longleftrightarrow> n dvd m"
by (metis lcm_proj1_if_dvd_nat lcm_unique_nat)

lemma lcm_proj2_iff_nat[simp]: "lcm m n = (n::nat) \<longleftrightarrow> m dvd n"
by (metis lcm_proj2_if_dvd_nat lcm_unique_nat)

lemma lcm_proj1_iff_int[simp]: "lcm m n = abs(m::int) \<longleftrightarrow> n dvd m"
by (metis dvd_abs_iff lcm_proj1_if_dvd_int lcm_unique_int)

lemma lcm_proj2_iff_int[simp]: "lcm m n = abs(n::int) \<longleftrightarrow> m dvd n"
by (metis dvd_abs_iff lcm_proj2_if_dvd_int lcm_unique_int)

lemma lcm_assoc_nat: "lcm (lcm n m) (p::nat) = lcm n (lcm m p)"
by(rule lcm_unique_nat[THEN iffD1])(metis dvd.order_trans lcm_unique_nat)

lemma lcm_assoc_int: "lcm (lcm n m) (p::int) = lcm n (lcm m p)"
by(rule lcm_unique_int[THEN iffD1])(metis dvd_trans lcm_unique_int)

lemmas lcm_left_commute_nat = mk_left_commute[of lcm, OF lcm_assoc_nat lcm_commute_nat]
lemmas lcm_left_commute_int = mk_left_commute[of lcm, OF lcm_assoc_int lcm_commute_int]

lemmas lcm_ac_nat = lcm_assoc_nat lcm_commute_nat lcm_left_commute_nat
lemmas lcm_ac_int = lcm_assoc_int lcm_commute_int lcm_left_commute_int

lemma fun_left_comm_idem_gcd_nat: "fun_left_comm_idem (gcd :: nat\<Rightarrow>nat\<Rightarrow>nat)"
proof qed (auto simp add: gcd_ac_nat)

lemma fun_left_comm_idem_gcd_int: "fun_left_comm_idem (gcd :: int\<Rightarrow>int\<Rightarrow>int)"
proof qed (auto simp add: gcd_ac_int)

lemma fun_left_comm_idem_lcm_nat: "fun_left_comm_idem (lcm :: nat\<Rightarrow>nat\<Rightarrow>nat)"
proof qed (auto simp add: lcm_ac_nat)

lemma fun_left_comm_idem_lcm_int: "fun_left_comm_idem (lcm :: int\<Rightarrow>int\<Rightarrow>int)"
proof qed (auto simp add: lcm_ac_int)


(* FIXME introduce selimattice_bot/top and derive the following lemmas in there: *)

lemma lcm_0_iff_nat[simp]: "lcm (m::nat) n = 0 \<longleftrightarrow> m=0 \<or> n=0"
by (metis lcm_0_left_nat lcm_0_nat mult_is_0 prod_gcd_lcm_nat)

lemma lcm_0_iff_int[simp]: "lcm (m::int) n = 0 \<longleftrightarrow> m=0 \<or> n=0"
by (metis lcm_0_int lcm_0_left_int lcm_pos_int zless_le)

lemma lcm_1_iff_nat[simp]: "lcm (m::nat) n = 1 \<longleftrightarrow> m=1 \<and> n=1"
by (metis gcd_1_nat lcm_unique_nat nat_mult_1 prod_gcd_lcm_nat)

lemma lcm_1_iff_int[simp]: "lcm (m::int) n = 1 \<longleftrightarrow> (m=1 \<or> m = -1) \<and> (n=1 \<or> n = -1)"
by (auto simp add: abs_mult_self trans [OF lcm_unique_int eq_commute, symmetric] zmult_eq_1_iff)


subsection {* Primes *}

(* FIXME Is there a better way to handle these, rather than making them elim rules? *)

lemma prime_ge_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= 0"
  by (unfold prime_nat_def, auto)

lemma prime_gt_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p > 0"
  by (unfold prime_nat_def, auto)

lemma prime_ge_1_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= 1"
  by (unfold prime_nat_def, auto)

lemma prime_gt_1_nat [elim]: "prime (p::nat) \<Longrightarrow> p > 1"
  by (unfold prime_nat_def, auto)

lemma prime_ge_Suc_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= Suc 0"
  by (unfold prime_nat_def, auto)

lemma prime_gt_Suc_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p > Suc 0"
  by (unfold prime_nat_def, auto)

lemma prime_ge_2_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= 2"
  by (unfold prime_nat_def, auto)

lemma prime_ge_0_int [elim]: "prime (p::int) \<Longrightarrow> p >= 0"
  by (unfold prime_int_def prime_nat_def) auto

lemma prime_gt_0_int [elim]: "prime (p::int) \<Longrightarrow> p > 0"
  by (unfold prime_int_def prime_nat_def, auto)

lemma prime_ge_1_int [elim]: "prime (p::int) \<Longrightarrow> p >= 1"
  by (unfold prime_int_def prime_nat_def, auto)

lemma prime_gt_1_int [elim]: "prime (p::int) \<Longrightarrow> p > 1"
  by (unfold prime_int_def prime_nat_def, auto)

lemma prime_ge_2_int [elim]: "prime (p::int) \<Longrightarrow> p >= 2"
  by (unfold prime_int_def prime_nat_def, auto)


lemma prime_int_altdef: "prime (p::int) = (1 < p \<and> (\<forall>m \<ge> 0. m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  using prime_nat_def [transferred]
    apply (case_tac "p >= 0")
    by (blast, auto simp add: prime_ge_0_int)

(* To do: determine primality of any numeral *)

lemma zero_not_prime_nat [simp]: "~prime (0::nat)"
  by (simp add: prime_nat_def)

lemma zero_not_prime_int [simp]: "~prime (0::int)"
  by (simp add: prime_int_def)

lemma one_not_prime_nat [simp]: "~prime (1::nat)"
  by (simp add: prime_nat_def)

lemma Suc_0_not_prime_nat [simp]: "~prime (Suc 0)"
  by (simp add: prime_nat_def One_nat_def)

lemma one_not_prime_int [simp]: "~prime (1::int)"
  by (simp add: prime_int_def)

lemma two_is_prime_nat [simp]: "prime (2::nat)"
  apply (auto simp add: prime_nat_def)
  apply (case_tac m)
  apply (auto dest!: dvd_imp_le)
  done

lemma two_is_prime_int [simp]: "prime (2::int)"
  by (rule two_is_prime_nat [transferred direction: nat "op <= (0::int)"])

lemma prime_imp_coprime_nat: "prime (p::nat) \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_nat_def)
  apply (metis gcd_dvd1_nat gcd_dvd2_nat)
  done

lemma prime_imp_coprime_int: "prime (p::int) \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_int_altdef)
  apply (metis gcd_dvd1_int gcd_dvd2_int gcd_ge_0_int)
  done

lemma prime_dvd_mult_nat: "prime (p::nat) \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: coprime_dvd_mult_nat prime_imp_coprime_nat)

lemma prime_dvd_mult_int: "prime (p::int) \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: coprime_dvd_mult_int prime_imp_coprime_int)

lemma prime_dvd_mult_eq_nat [simp]: "prime (p::nat) \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule prime_dvd_mult_nat, auto)

lemma prime_dvd_mult_eq_int [simp]: "prime (p::int) \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule prime_dvd_mult_int, auto)

lemma not_prime_eq_prod_nat: "(n::nat) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_nat_def dvd_def apply auto
  by(metis mult_commute linorder_neq_iff linorder_not_le mult_1 n_less_n_mult_m one_le_mult_iff less_imp_le_nat)

lemma not_prime_eq_prod_int: "(n::int) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_int_altdef dvd_def
  apply auto
  by(metis div_mult_self1_is_id div_mult_self2_is_id int_div_less_self int_one_le_iff_zero_less zero_less_mult_pos zless_le)

lemma prime_dvd_power_nat [rule_format]: "prime (p::nat) -->
    n > 0 --> (p dvd x^n --> p dvd x)"
  by (induct n rule: nat_induct, auto)

lemma prime_dvd_power_int [rule_format]: "prime (p::int) -->
    n > 0 --> (p dvd x^n --> p dvd x)"
  apply (induct n rule: nat_induct, auto)
  apply (frule prime_ge_0_int)
  apply auto
done

lemma prime_imp_power_coprime_nat: "prime (p::nat) \<Longrightarrow> ~ p dvd a \<Longrightarrow>
    coprime a (p^m)"
  apply (rule coprime_exp_nat)
  apply (subst gcd_commute_nat)
  apply (erule (1) prime_imp_coprime_nat)
done

lemma prime_imp_power_coprime_int: "prime (p::int) \<Longrightarrow> ~ p dvd a \<Longrightarrow>
    coprime a (p^m)"
  apply (rule coprime_exp_int)
  apply (subst gcd_commute_int)
  apply (erule (1) prime_imp_coprime_int)
done

lemma primes_coprime_nat: "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  apply (rule prime_imp_coprime_nat, assumption)
  apply (unfold prime_nat_def, auto)
done

lemma primes_coprime_int: "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  apply (rule prime_imp_coprime_int, assumption)
  apply (unfold prime_int_altdef, clarify)
  apply (drule_tac x = q in spec)
  apply (drule_tac x = p in spec)
  apply auto
done

lemma primes_imp_powers_coprime_nat: "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow>
    coprime (p^m) (q^n)"
  by (rule coprime_exp2_nat, rule primes_coprime_nat)

lemma primes_imp_powers_coprime_int: "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow>
    coprime (p^m) (q^n)"
  by (rule coprime_exp2_int, rule primes_coprime_int)

lemma prime_factor_nat: "n \<noteq> (1::nat) \<Longrightarrow> \<exists> p. prime p \<and> p dvd n"
  apply (induct n rule: nat_less_induct)
  apply (case_tac "n = 0")
  using two_is_prime_nat apply blast
  apply (case_tac "prime n")
  apply blast
  apply (subgoal_tac "n > 1")
  apply (frule (1) not_prime_eq_prod_nat)
  apply (auto intro: dvd_mult dvd_mult2)
done

(* An Isar version:

lemma prime_factor_b_nat:
  fixes n :: nat
  assumes "n \<noteq> 1"
  shows "\<exists>p. prime p \<and> p dvd n"

using `n ~= 1`
proof (induct n rule: less_induct_nat)
  fix n :: nat
  assume "n ~= 1" and
    ih: "\<forall>m<n. m \<noteq> 1 \<longrightarrow> (\<exists>p. prime p \<and> p dvd m)"
  thus "\<exists>p. prime p \<and> p dvd n"
  proof -
  {
    assume "n = 0"
    moreover note two_is_prime_nat
    ultimately have ?thesis
      by (auto simp del: two_is_prime_nat)
  }
  moreover
  {
    assume "prime n"
    hence ?thesis by auto
  }
  moreover
  {
    assume "n ~= 0" and "~ prime n"
    with `n ~= 1` have "n > 1" by auto
    with `~ prime n` and not_prime_eq_prod_nat obtain m k where
      "n = m * k" and "1 < m" and "m < n" by blast
    with ih obtain p where "prime p" and "p dvd m" by blast
    with `n = m * k` have ?thesis by auto
  }
  ultimately show ?thesis by blast
  qed
qed

*)

text {* One property of coprimality is easier to prove via prime factors. *}

lemma prime_divprod_pow_nat:
  assumes p: "prime (p::nat)" and ab: "coprime a b" and pab: "p^n dvd a * b"
  shows "p^n dvd a \<or> p^n dvd b"
proof-
  {assume "n = 0 \<or> a = 1 \<or> b = 1" with pab have ?thesis
      apply (cases "n=0", simp_all)
      apply (cases "a=1", simp_all) done}
  moreover
  {assume n: "n \<noteq> 0" and a: "a\<noteq>1" and b: "b\<noteq>1"
    then obtain m where m: "n = Suc m" by (cases n, auto)
    from n have "p dvd p^n" by (intro dvd_power, auto)
    also note pab
    finally have pab': "p dvd a * b".
    from prime_dvd_mult_nat[OF p pab']
    have "p dvd a \<or> p dvd b" .
    moreover
    {assume pa: "p dvd a"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
      from coprime_common_divisor_nat [OF ab, OF pa] p have "\<not> p dvd b" by auto
      with p have "coprime b p"
        by (subst gcd_commute_nat, intro prime_imp_coprime_nat)
      hence pnb: "coprime (p^n) b"
        by (subst gcd_commute_nat, rule coprime_exp_nat)
      from coprime_divprod_nat[OF pnba pnb] have ?thesis by blast }
    moreover
    {assume pb: "p dvd b"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
      from coprime_common_divisor_nat [OF ab, of p] pb p have "\<not> p dvd a"
        by auto
      with p have "coprime a p"
        by (subst gcd_commute_nat, intro prime_imp_coprime_nat)
      hence pna: "coprime (p^n) a"
        by (subst gcd_commute_nat, rule coprime_exp_nat)
      from coprime_divprod_nat[OF pab pna] have ?thesis by blast }
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

end
