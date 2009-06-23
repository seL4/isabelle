(*  Title:      GCD.thy
    Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad


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

*)


header {* GCD *}

theory GCD
imports NatTransfer
begin

declare One_nat_def [simp del]

subsection {* gcd *}

class gcd = one +

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
lemma nat_gcd_induct:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
  apply (rule gcd_nat.induct)
  apply (case_tac "y = 0")
  using assms apply simp_all
done

(* specific to int *)

lemma int_gcd_neg1 [simp]: "gcd (-x::int) y = gcd x y"
  by (simp add: gcd_int_def)

lemma int_gcd_neg2 [simp]: "gcd (x::int) (-y) = gcd x y"
  by (simp add: gcd_int_def)

lemma int_gcd_abs: "gcd (x::int) y = gcd (abs x) (abs y)"
  by (simp add: gcd_int_def)

lemma int_gcd_cases:
  fixes x :: int and y
  assumes "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (gcd x y)"
      and "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (gcd x (-y))"
      and "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (gcd (-x) y)"
      and "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (gcd (-x) (-y))"
  shows "P (gcd x y)"
by (insert prems, auto simp add: int_gcd_neg1 int_gcd_neg2, arith)

lemma int_gcd_ge_0 [simp]: "gcd (x::int) y >= 0"
  by (simp add: gcd_int_def)

lemma int_lcm_neg1: "lcm (-x::int) y = lcm x y"
  by (simp add: lcm_int_def)

lemma int_lcm_neg2: "lcm (x::int) (-y) = lcm x y"
  by (simp add: lcm_int_def)

lemma int_lcm_abs: "lcm (x::int) y = lcm (abs x) (abs y)"
  by (simp add: lcm_int_def)

lemma int_lcm_cases:
  fixes x :: int and y
  assumes "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm x y)"
      and "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm x (-y))"
      and "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm (-x) y)"
      and "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm (-x) (-y))"
  shows "P (lcm x y)"
by (insert prems, auto simp add: int_lcm_neg1 int_lcm_neg2, arith)

lemma int_lcm_ge_0 [simp]: "lcm (x::int) y >= 0"
  by (simp add: lcm_int_def)

(* was gcd_0, etc. *)
lemma nat_gcd_0 [simp]: "gcd (x::nat) 0 = x"
  by simp

(* was igcd_0, etc. *)
lemma int_gcd_0 [simp]: "gcd (x::int) 0 = abs x"
  by (unfold gcd_int_def, auto)

lemma nat_gcd_0_left [simp]: "gcd 0 (x::nat) = x"
  by simp

lemma int_gcd_0_left [simp]: "gcd 0 (x::int) = abs x"
  by (unfold gcd_int_def, auto)

lemma nat_gcd_red: "gcd (x::nat) y = gcd y (x mod y)"
  by (case_tac "y = 0", auto)

(* weaker, but useful for the simplifier *)

lemma nat_gcd_non_0: "y ~= (0::nat) \<Longrightarrow> gcd (x::nat) y = gcd y (x mod y)"
  by simp

lemma nat_gcd_1 [simp]: "gcd (m::nat) 1 = 1"
  by simp

lemma nat_gcd_Suc_0 [simp]: "gcd (m::nat) (Suc 0) = Suc 0"
  by (simp add: One_nat_def)

lemma int_gcd_1 [simp]: "gcd (m::int) 1 = 1"
  by (simp add: gcd_int_def)

lemma nat_gcd_self [simp]: "gcd (x::nat) x = x"
  by simp

lemma int_gcd_def [simp]: "gcd (x::int) x = abs x"
  by (subst int_gcd_abs, auto simp add: gcd_int_def)

declare gcd_nat.simps [simp del]

text {*
  \medskip @{term "gcd m n"} divides @{text m} and @{text n}.  The
  conjunctions don't seem provable separately.
*}

lemma nat_gcd_dvd1 [iff]: "(gcd (m::nat)) n dvd m"
  and nat_gcd_dvd2 [iff]: "(gcd m n) dvd n"
  apply (induct m n rule: nat_gcd_induct)
  apply (simp_all add: nat_gcd_non_0)
  apply (blast dest: dvd_mod_imp_dvd)
done

thm nat_gcd_dvd1 [transferred]

lemma int_gcd_dvd1 [iff]: "gcd (x::int) y dvd x"
  apply (subst int_gcd_abs)
  apply (rule dvd_trans)
  apply (rule nat_gcd_dvd1 [transferred])
  apply auto
done

lemma int_gcd_dvd2 [iff]: "gcd (x::int) y dvd y"
  apply (subst int_gcd_abs)
  apply (rule dvd_trans)
  apply (rule nat_gcd_dvd2 [transferred])
  apply auto
done

lemma dvd_gcd_D1_nat: "k dvd gcd m n \<Longrightarrow> (k::nat) dvd m"
by(metis nat_gcd_dvd1 dvd_trans)

lemma dvd_gcd_D2_nat: "k dvd gcd m n \<Longrightarrow> (k::nat) dvd n"
by(metis nat_gcd_dvd2 dvd_trans)

lemma dvd_gcd_D1_int: "i dvd gcd m n \<Longrightarrow> (i::int) dvd m"
by(metis int_gcd_dvd1 dvd_trans)

lemma dvd_gcd_D2_int: "i dvd gcd m n \<Longrightarrow> (i::int) dvd n"
by(metis int_gcd_dvd2 dvd_trans)

lemma nat_gcd_le1 [simp]: "a \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> a"
  by (rule dvd_imp_le, auto)

lemma nat_gcd_le2 [simp]: "b \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> b"
  by (rule dvd_imp_le, auto)

lemma int_gcd_le1 [simp]: "a > 0 \<Longrightarrow> gcd (a::int) b \<le> a"
  by (rule zdvd_imp_le, auto)

lemma int_gcd_le2 [simp]: "b > 0 \<Longrightarrow> gcd (a::int) b \<le> b"
  by (rule zdvd_imp_le, auto)

lemma nat_gcd_greatest: "(k::nat) dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd gcd m n"
  by (induct m n rule: nat_gcd_induct) (simp_all add: nat_gcd_non_0 dvd_mod)

lemma int_gcd_greatest:
  assumes "(k::int) dvd m" and "k dvd n"
  shows "k dvd gcd m n"

  apply (subst int_gcd_abs)
  apply (subst abs_dvd_iff [symmetric])
  apply (rule nat_gcd_greatest [transferred])
  using prems apply auto
done

lemma nat_gcd_greatest_iff [iff]: "(k dvd gcd (m::nat) n) =
    (k dvd m & k dvd n)"
  by (blast intro!: nat_gcd_greatest intro: dvd_trans)

lemma int_gcd_greatest_iff: "((k::int) dvd gcd m n) = (k dvd m & k dvd n)"
  by (blast intro!: int_gcd_greatest intro: dvd_trans)

lemma nat_gcd_zero [simp]: "(gcd (m::nat) n = 0) = (m = 0 & n = 0)"
  by (simp only: dvd_0_left_iff [symmetric] nat_gcd_greatest_iff)

lemma int_gcd_zero [simp]: "(gcd (m::int) n = 0) = (m = 0 & n = 0)"
  by (auto simp add: gcd_int_def)

lemma nat_gcd_pos [simp]: "(gcd (m::nat) n > 0) = (m ~= 0 | n ~= 0)"
  by (insert nat_gcd_zero [of m n], arith)

lemma int_gcd_pos [simp]: "(gcd (m::int) n > 0) = (m ~= 0 | n ~= 0)"
  by (insert int_gcd_zero [of m n], insert int_gcd_ge_0 [of m n], arith)

lemma nat_gcd_commute: "gcd (m::nat) n = gcd n m"
  by (rule dvd_anti_sym, auto)

lemma int_gcd_commute: "gcd (m::int) n = gcd n m"
  by (auto simp add: gcd_int_def nat_gcd_commute)

lemma nat_gcd_assoc: "gcd (gcd (k::nat) m) n = gcd k (gcd m n)"
  apply (rule dvd_anti_sym)
  apply (blast intro: dvd_trans)+
done

lemma int_gcd_assoc: "gcd (gcd (k::int) m) n = gcd k (gcd m n)"
  by (auto simp add: gcd_int_def nat_gcd_assoc)

lemmas nat_gcd_left_commute =
  mk_left_commute[of gcd, OF nat_gcd_assoc nat_gcd_commute]

lemmas int_gcd_left_commute =
  mk_left_commute[of gcd, OF int_gcd_assoc int_gcd_commute]

lemmas nat_gcd_ac = nat_gcd_assoc nat_gcd_commute nat_gcd_left_commute
  -- {* gcd is an AC-operator *}

lemmas int_gcd_ac = int_gcd_assoc int_gcd_commute int_gcd_left_commute

lemma nat_gcd_1_left [simp]: "gcd (1::nat) m = 1"
  by (subst nat_gcd_commute, simp)

lemma nat_gcd_Suc_0_left [simp]: "gcd (Suc 0) m = Suc 0"
  by (subst nat_gcd_commute, simp add: One_nat_def)

lemma int_gcd_1_left [simp]: "gcd (1::int) m = 1"
  by (subst int_gcd_commute, simp)

lemma nat_gcd_unique: "(d::nat) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  apply auto
  apply (rule dvd_anti_sym)
  apply (erule (1) nat_gcd_greatest)
  apply auto
done

lemma int_gcd_unique: "d >= 0 & (d::int) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  apply (case_tac "d = 0")
  apply force
  apply (rule iffI)
  apply (rule zdvd_anti_sym)
  apply arith
  apply (subst int_gcd_pos)
  apply clarsimp
  apply (drule_tac x = "d + 1" in spec)
  apply (frule zdvd_imp_le)
  apply (auto intro: int_gcd_greatest)
done

text {*
  \medskip Multiplication laws
*}

lemma nat_gcd_mult_distrib: "(k::nat) * gcd m n = gcd (k * m) (k * n)"
    -- {* \cite[page 27]{davenport92} *}
  apply (induct m n rule: nat_gcd_induct)
  apply simp
  apply (case_tac "k = 0")
  apply (simp_all add: mod_geq nat_gcd_non_0 mod_mult_distrib2)
done

lemma int_gcd_mult_distrib: "abs (k::int) * gcd m n = gcd (k * m) (k * n)"
  apply (subst (1 2) int_gcd_abs)
  apply (simp add: abs_mult)
  apply (rule nat_gcd_mult_distrib [transferred])
  apply auto
done

lemma nat_gcd_mult [simp]: "gcd (k::nat) (k * n) = k"
  by (rule nat_gcd_mult_distrib [of k 1 n, simplified, symmetric])

lemma int_gcd_mult [simp]: "gcd (k::int) (k * n) = abs k"
  by (rule int_gcd_mult_distrib [of k 1 n, simplified, symmetric])

lemma nat_coprime_dvd_mult: "coprime (k::nat) n \<Longrightarrow> k dvd m * n \<Longrightarrow> k dvd m"
  apply (insert nat_gcd_mult_distrib [of m k n])
  apply simp
  apply (erule_tac t = m in ssubst)
  apply simp
  done

lemma int_coprime_dvd_mult:
  assumes "coprime (k::int) n" and "k dvd m * n"
  shows "k dvd m"

  using prems
  apply (subst abs_dvd_iff [symmetric])
  apply (subst dvd_abs_iff [symmetric])
  apply (subst (asm) int_gcd_abs)
  apply (rule nat_coprime_dvd_mult [transferred])
  apply auto
  apply (subst abs_mult [symmetric], auto)
done

lemma nat_coprime_dvd_mult_iff: "coprime (k::nat) n \<Longrightarrow>
    (k dvd m * n) = (k dvd m)"
  by (auto intro: nat_coprime_dvd_mult)

lemma int_coprime_dvd_mult_iff: "coprime (k::int) n \<Longrightarrow>
    (k dvd m * n) = (k dvd m)"
  by (auto intro: int_coprime_dvd_mult)

lemma nat_gcd_mult_cancel: "coprime k n \<Longrightarrow> gcd ((k::nat) * m) n = gcd m n"
  apply (rule dvd_anti_sym)
  apply (rule nat_gcd_greatest)
  apply (rule_tac n = k in nat_coprime_dvd_mult)
  apply (simp add: nat_gcd_assoc)
  apply (simp add: nat_gcd_commute)
  apply (simp_all add: mult_commute)
done

lemma int_gcd_mult_cancel:
  assumes "coprime (k::int) n"
  shows "gcd (k * m) n = gcd m n"

  using prems
  apply (subst (1 2) int_gcd_abs)
  apply (subst abs_mult)
  apply (rule nat_gcd_mult_cancel [transferred])
  apply (auto simp add: int_gcd_abs [symmetric])
done

text {* \medskip Addition laws *}

lemma nat_gcd_add1 [simp]: "gcd ((m::nat) + n) n = gcd m n"
  apply (case_tac "n = 0")
  apply (simp_all add: nat_gcd_non_0)
done

lemma nat_gcd_add2 [simp]: "gcd (m::nat) (m + n) = gcd m n"
  apply (subst (1 2) nat_gcd_commute)
  apply (subst add_commute)
  apply simp
done

(* to do: add the other variations? *)

lemma nat_gcd_diff1: "(m::nat) >= n \<Longrightarrow> gcd (m - n) n = gcd m n"
  by (subst nat_gcd_add1 [symmetric], auto)

lemma nat_gcd_diff2: "(n::nat) >= m \<Longrightarrow> gcd (n - m) n = gcd m n"
  apply (subst nat_gcd_commute)
  apply (subst nat_gcd_diff1 [symmetric])
  apply auto
  apply (subst nat_gcd_commute)
  apply (subst nat_gcd_diff1)
  apply assumption
  apply (rule nat_gcd_commute)
done

lemma int_gcd_non_0: "(y::int) > 0 \<Longrightarrow> gcd x y = gcd y (x mod y)"
  apply (frule_tac b = y and a = x in pos_mod_sign)
  apply (simp del: pos_mod_sign add: gcd_int_def abs_if nat_mod_distrib)
  apply (auto simp add: nat_gcd_non_0 nat_mod_distrib [symmetric]
    zmod_zminus1_eq_if)
  apply (frule_tac a = x in pos_mod_bound)
  apply (subst (1 2) nat_gcd_commute)
  apply (simp del: pos_mod_bound add: nat_diff_distrib nat_gcd_diff2
    nat_le_eq_zle)
done

lemma int_gcd_red: "gcd (x::int) y = gcd y (x mod y)"
  apply (case_tac "y = 0")
  apply force
  apply (case_tac "y > 0")
  apply (subst int_gcd_non_0, auto)
  apply (insert int_gcd_non_0 [of "-y" "-x"])
  apply (auto simp add: int_gcd_neg1 int_gcd_neg2)
done

lemma int_gcd_add1 [simp]: "gcd ((m::int) + n) n = gcd m n"
  apply (case_tac "n = 0", force)
  apply (subst (1 2) int_gcd_red)
  apply auto
done

lemma int_gcd_add2 [simp]: "gcd m ((m::int) + n) = gcd m n"
  apply (subst int_gcd_commute)
  apply (subst add_commute)
  apply (subst int_gcd_add1)
  apply (subst int_gcd_commute)
  apply (rule refl)
done

lemma nat_gcd_add_mult: "gcd (m::nat) (k * m + n) = gcd m n"
  by (induct k, simp_all add: ring_simps)

lemma int_gcd_add_mult: "gcd (m::int) (k * m + n) = gcd m n"
  apply (subgoal_tac "ALL s. ALL m. ALL n.
      gcd m (int (s::nat) * m + n) = gcd m n")
  apply (case_tac "k >= 0")
  apply (drule_tac x = "nat k" in spec, force)
  apply (subst (1 2) int_gcd_neg2 [symmetric])
  apply (drule_tac x = "nat (- k)" in spec)
  apply (drule_tac x = "m" in spec)
  apply (drule_tac x = "-n" in spec)
  apply auto
  apply (rule nat_induct)
  apply auto
  apply (auto simp add: left_distrib)
  apply (subst add_assoc)
  apply simp
done

(* to do: differences, and all variations of addition rules
    as simplification rules for nat and int *)

lemma nat_gcd_dvd_prod [iff]: "gcd (m::nat) n dvd k * n"
  using mult_dvd_mono [of 1] by auto

(* to do: add the three variations of these, and for ints? *)

lemma finite_divisors_nat:
  assumes "(m::nat)~= 0" shows "finite{d. d dvd m}"
proof-
  have "finite{d. d <= m}" by(blast intro: bounded_nat_set_is_finite)
  from finite_subset[OF _ this] show ?thesis using assms
    by(bestsimp intro!:dvd_imp_le)
qed

lemma finite_divisors_int:
  assumes "(i::int) ~= 0" shows "finite{d. d dvd i}"
proof-
  have "{d. abs d <= abs i} = {- abs i .. abs i}" by(auto simp:abs_if)
  hence "finite{d. abs d <= abs i}" by simp
  from finite_subset[OF _ this] show ?thesis using assms
    by(bestsimp intro!:dvd_imp_le_int)
qed

lemma gcd_is_Max_divisors_nat:
  "m ~= 0 \<Longrightarrow> n ~= 0 \<Longrightarrow> gcd (m::nat) n = (Max {d. d dvd m & d dvd n})"
apply(rule Max_eqI[THEN sym])
  apply (metis dvd.eq_iff finite_Collect_conjI finite_divisors_nat)
 apply simp
 apply(metis Suc_diff_1 Suc_neq_Zero dvd_imp_le nat_gcd_greatest_iff nat_gcd_pos)
apply simp
done

lemma gcd_is_Max_divisors_int:
  "m ~= 0 ==> n ~= 0 ==> gcd (m::int) n = (Max {d. d dvd m & d dvd n})"
apply(rule Max_eqI[THEN sym])
  apply (metis dvd.eq_iff finite_Collect_conjI finite_divisors_int)
 apply simp
 apply (metis int_gcd_greatest_iff int_gcd_pos zdvd_imp_le)
apply simp
done


subsection {* Coprimality *}

lemma nat_div_gcd_coprime [intro]:
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
  have "?g \<noteq> 0" using nz by (simp add: nat_gcd_zero)
  then have gp: "?g > 0" by arith
  from nat_gcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  with dvd_mult_cancel1 [OF gp] show "?g' = 1" by simp
qed

lemma int_div_gcd_coprime [intro]:
  assumes nz: "(a::int) \<noteq> 0 \<or> b \<noteq> 0"
  shows "coprime (a div gcd a b) (b div gcd a b)"

  apply (subst (1 2 3) int_gcd_abs)
  apply (subst (1 2) abs_div)
  apply auto
  prefer 3
  apply (rule nat_div_gcd_coprime [transferred])
  using nz apply (auto simp add: int_gcd_abs [symmetric])
done

lemma nat_coprime: "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using nat_gcd_unique[of 1 a b, simplified] by auto

lemma nat_coprime_Suc_0:
    "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = Suc 0)"
  using nat_coprime by (simp add: One_nat_def)

lemma int_coprime: "coprime (a::int) b \<longleftrightarrow>
    (\<forall>d. d >= 0 \<and> d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using int_gcd_unique [of 1 a b]
  apply clarsimp
  apply (erule subst)
  apply (rule iffI)
  apply force
  apply (drule_tac x = "abs e" in exI)
  apply (case_tac "e >= 0")
  apply force
  apply force
done

lemma nat_gcd_coprime:
  assumes z: "gcd (a::nat) b \<noteq> 0" and a: "a = a' * gcd a b" and
    b: "b = b' * gcd a b"
  shows    "coprime a' b'"

  apply (subgoal_tac "a' = a div gcd a b")
  apply (erule ssubst)
  apply (subgoal_tac "b' = b div gcd a b")
  apply (erule ssubst)
  apply (rule nat_div_gcd_coprime)
  using prems
  apply force
  apply (subst (1) b)
  using z apply force
  apply (subst (1) a)
  using z apply force
done

lemma int_gcd_coprime:
  assumes z: "gcd (a::int) b \<noteq> 0" and a: "a = a' * gcd a b" and
    b: "b = b' * gcd a b"
  shows    "coprime a' b'"

  apply (subgoal_tac "a' = a div gcd a b")
  apply (erule ssubst)
  apply (subgoal_tac "b' = b div gcd a b")
  apply (erule ssubst)
  apply (rule int_div_gcd_coprime)
  using prems
  apply force
  apply (subst (1) b)
  using z apply force
  apply (subst (1) a)
  using z apply force
done

lemma nat_coprime_mult: assumes da: "coprime (d::nat) a" and db: "coprime d b"
    shows "coprime d (a * b)"
  apply (subst nat_gcd_commute)
  using da apply (subst nat_gcd_mult_cancel)
  apply (subst nat_gcd_commute, assumption)
  apply (subst nat_gcd_commute, rule db)
done

lemma int_coprime_mult: assumes da: "coprime (d::int) a" and db: "coprime d b"
    shows "coprime d (a * b)"
  apply (subst int_gcd_commute)
  using da apply (subst int_gcd_mult_cancel)
  apply (subst int_gcd_commute, assumption)
  apply (subst int_gcd_commute, rule db)
done

lemma nat_coprime_lmult:
  assumes dab: "coprime (d::nat) (a * b)" shows "coprime d a"
proof -
  have "gcd d a dvd gcd d (a * b)"
    by (rule nat_gcd_greatest, auto)
  with dab show ?thesis
    by auto
qed

lemma int_coprime_lmult:
  assumes dab: "coprime (d::int) (a * b)" shows "coprime d a"
proof -
  have "gcd d a dvd gcd d (a * b)"
    by (rule int_gcd_greatest, auto)
  with dab show ?thesis
    by auto
qed

lemma nat_coprime_rmult:
  assumes dab: "coprime (d::nat) (a * b)" shows "coprime d b"
proof -
  have "gcd d b dvd gcd d (a * b)"
    by (rule nat_gcd_greatest, auto intro: dvd_mult)
  with dab show ?thesis
    by auto
qed

lemma int_coprime_rmult:
  assumes dab: "coprime (d::int) (a * b)" shows "coprime d b"
proof -
  have "gcd d b dvd gcd d (a * b)"
    by (rule int_gcd_greatest, auto intro: dvd_mult)
  with dab show ?thesis
    by auto
qed

lemma nat_coprime_mul_eq: "coprime (d::nat) (a * b) \<longleftrightarrow>
    coprime d a \<and>  coprime d b"
  using nat_coprime_rmult[of d a b] nat_coprime_lmult[of d a b]
    nat_coprime_mult[of d a b]
  by blast

lemma int_coprime_mul_eq: "coprime (d::int) (a * b) \<longleftrightarrow>
    coprime d a \<and>  coprime d b"
  using int_coprime_rmult[of d a b] int_coprime_lmult[of d a b]
    int_coprime_mult[of d a b]
  by blast

lemma nat_gcd_coprime_exists:
    assumes nz: "gcd (a::nat) b \<noteq> 0"
    shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
  apply (rule_tac x = "a div gcd a b" in exI)
  apply (rule_tac x = "b div gcd a b" in exI)
  using nz apply (auto simp add: nat_div_gcd_coprime dvd_div_mult)
done

lemma int_gcd_coprime_exists:
    assumes nz: "gcd (a::int) b \<noteq> 0"
    shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
  apply (rule_tac x = "a div gcd a b" in exI)
  apply (rule_tac x = "b div gcd a b" in exI)
  using nz apply (auto simp add: int_div_gcd_coprime dvd_div_mult_self)
done

lemma nat_coprime_exp: "coprime (d::nat) a \<Longrightarrow> coprime d (a^n)"
  by (induct n, simp_all add: nat_coprime_mult)

lemma int_coprime_exp: "coprime (d::int) a \<Longrightarrow> coprime d (a^n)"
  by (induct n, simp_all add: int_coprime_mult)

lemma nat_coprime_exp2 [intro]: "coprime (a::nat) b \<Longrightarrow> coprime (a^n) (b^m)"
  apply (rule nat_coprime_exp)
  apply (subst nat_gcd_commute)
  apply (rule nat_coprime_exp)
  apply (subst nat_gcd_commute, assumption)
done

lemma int_coprime_exp2 [intro]: "coprime (a::int) b \<Longrightarrow> coprime (a^n) (b^m)"
  apply (rule int_coprime_exp)
  apply (subst int_gcd_commute)
  apply (rule int_coprime_exp)
  apply (subst int_gcd_commute, assumption)
done

lemma nat_gcd_exp: "gcd ((a::nat)^n) (b^n) = (gcd a b)^n"
proof (cases)
  assume "a = 0 & b = 0"
  thus ?thesis by simp
  next assume "~(a = 0 & b = 0)"
  hence "coprime ((a div gcd a b)^n) ((b div gcd a b)^n)"
    by auto
  hence "gcd ((a div gcd a b)^n * (gcd a b)^n)
      ((b div gcd a b)^n * (gcd a b)^n) = (gcd a b)^n"
    apply (subst (1 2) mult_commute)
    apply (subst nat_gcd_mult_distrib [symmetric])
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

lemma int_gcd_exp: "gcd ((a::int)^n) (b^n) = (gcd a b)^n"
  apply (subst (1 2) int_gcd_abs)
  apply (subst (1 2) power_abs)
  apply (rule nat_gcd_exp [where n = n, transferred])
  apply auto
done

lemma nat_coprime_divprod: "(d::nat) dvd a * b  \<Longrightarrow> coprime d a \<Longrightarrow> d dvd b"
  using nat_coprime_dvd_mult_iff[of d a b]
  by (auto simp add: mult_commute)

lemma int_coprime_divprod: "(d::int) dvd a * b  \<Longrightarrow> coprime d a \<Longrightarrow> d dvd b"
  using int_coprime_dvd_mult_iff[of d a b]
  by (auto simp add: mult_commute)

lemma nat_division_decomp: assumes dc: "(a::nat) dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof-
  let ?g = "gcd a b"
  {assume "?g = 0" with dc have ?thesis by auto}
  moreover
  {assume z: "?g \<noteq> 0"
    from nat_gcd_coprime_exists[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
      by blast
    have thb: "?g dvd b" by auto
    from ab'(1) have "a' dvd a"  unfolding dvd_def by blast
    with dc have th0: "a' dvd b*c" using dvd_trans[of a' a "b*c"] by simp
    from dc ab'(1,2) have "a'*?g dvd (b'*?g) *c" by auto
    hence "?g*a' dvd ?g * (b' * c)" by (simp add: mult_assoc)
    with z have th_1: "a' dvd b' * c" by auto
    from nat_coprime_dvd_mult[OF ab'(3)] th_1
    have thc: "a' dvd c" by (subst (asm) mult_commute, blast)
    from ab' have "a = ?g*a'" by algebra
    with thb thc have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma int_division_decomp: assumes dc: "(a::int) dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof-
  let ?g = "gcd a b"
  {assume "?g = 0" with dc have ?thesis by auto}
  moreover
  {assume z: "?g \<noteq> 0"
    from int_gcd_coprime_exists[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
      by blast
    have thb: "?g dvd b" by auto
    from ab'(1) have "a' dvd a"  unfolding dvd_def by blast
    with dc have th0: "a' dvd b*c"
      using dvd_trans[of a' a "b*c"] by simp
    from dc ab'(1,2) have "a'*?g dvd (b'*?g) *c" by auto
    hence "?g*a' dvd ?g * (b' * c)" by (simp add: mult_assoc)
    with z have th_1: "a' dvd b' * c" by auto
    from int_coprime_dvd_mult[OF ab'(3)] th_1
    have thc: "a' dvd c" by (subst (asm) mult_commute, blast)
    from ab' have "a = ?g*a'" by algebra
    with thb thc have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma nat_pow_divides_pow:
  assumes ab: "(a::nat) ^ n dvd b ^n" and n:"n \<noteq> 0"
  shows "a dvd b"
proof-
  let ?g = "gcd a b"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  {assume "?g = 0" with ab n have ?thesis by auto }
  moreover
  {assume z: "?g \<noteq> 0"
    hence zn: "?g ^ n \<noteq> 0" using n by (simp add: neq0_conv)
    from nat_gcd_coprime_exists[OF z]
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
    from nat_coprime_dvd_mult[OF nat_coprime_exp [OF ab'(3), of m]] th1
    have "a' dvd b'" by (subst (asm) mult_commute, blast)
    hence "a'*?g dvd b'*?g" by simp
    with ab'(1,2)  have ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma int_pow_divides_pow:
  assumes ab: "(a::int) ^ n dvd b ^n" and n:"n \<noteq> 0"
  shows "a dvd b"
proof-
  let ?g = "gcd a b"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  {assume "?g = 0" with ab n have ?thesis by auto }
  moreover
  {assume z: "?g \<noteq> 0"
    hence zn: "?g ^ n \<noteq> 0" using n by (simp add: neq0_conv)
    from int_gcd_coprime_exists[OF z]
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
    from int_coprime_dvd_mult[OF int_coprime_exp [OF ab'(3), of m]] th1
    have "a' dvd b'" by (subst (asm) mult_commute, blast)
    hence "a'*?g dvd b'*?g" by simp
    with ab'(1,2)  have ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma nat_pow_divides_eq [simp]: "n ~= 0 \<Longrightarrow> ((a::nat)^n dvd b^n) = (a dvd b)"
  by (auto intro: nat_pow_divides_pow dvd_power_same)

lemma int_pow_divides_eq [simp]: "n ~= 0 \<Longrightarrow> ((a::int)^n dvd b^n) = (a dvd b)"
  by (auto intro: int_pow_divides_pow dvd_power_same)

lemma nat_divides_mult:
  assumes mr: "(m::nat) dvd r" and nr: "n dvd r" and mn:"coprime m n"
  shows "m * n dvd r"
proof-
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: mult_commute)
  hence "m dvd n'" using nat_coprime_dvd_mult_iff[OF mn] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  from n' k show ?thesis unfolding dvd_def by auto
qed

lemma int_divides_mult:
  assumes mr: "(m::int) dvd r" and nr: "n dvd r" and mn:"coprime m n"
  shows "m * n dvd r"
proof-
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: mult_commute)
  hence "m dvd n'" using int_coprime_dvd_mult_iff[OF mn] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  from n' k show ?thesis unfolding dvd_def by auto
qed

lemma nat_coprime_plus_one [simp]: "coprime ((n::nat) + 1) n"
  apply (subgoal_tac "gcd (n + 1) n dvd (n + 1 - n)")
  apply force
  apply (rule nat_dvd_diff)
  apply auto
done

lemma nat_coprime_Suc [simp]: "coprime (Suc n) n"
  using nat_coprime_plus_one by (simp add: One_nat_def)

lemma int_coprime_plus_one [simp]: "coprime ((n::int) + 1) n"
  apply (subgoal_tac "gcd (n + 1) n dvd (n + 1 - n)")
  apply force
  apply (rule dvd_diff)
  apply auto
done

lemma nat_coprime_minus_one: "(n::nat) \<noteq> 0 \<Longrightarrow> coprime (n - 1) n"
  using nat_coprime_plus_one [of "n - 1"]
    nat_gcd_commute [of "n - 1" n] by auto

lemma int_coprime_minus_one: "coprime ((n::int) - 1) n"
  using int_coprime_plus_one [of "n - 1"]
    int_gcd_commute [of "n - 1" n] by auto

lemma nat_setprod_coprime [rule_format]:
    "(ALL i: A. coprime (f i) (x::nat)) --> coprime (PROD i:A. f i) x"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto simp add: nat_gcd_mult_cancel)
done

lemma int_setprod_coprime [rule_format]:
    "(ALL i: A. coprime (f i) (x::int)) --> coprime (PROD i:A. f i) x"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto simp add: int_gcd_mult_cancel)
done

lemma nat_prime_odd: "prime (p::nat) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  unfolding prime_nat_def
  apply (subst even_mult_two_ex)
  apply clarify
  apply (drule_tac x = 2 in spec)
  apply auto
done

lemma int_prime_odd: "prime (p::int) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  unfolding prime_int_def
  apply (frule nat_prime_odd)
  apply (auto simp add: even_nat_def)
done

lemma nat_coprime_common_divisor: "coprime (a::nat) b \<Longrightarrow> x dvd a \<Longrightarrow>
    x dvd b \<Longrightarrow> x = 1"
  apply (subgoal_tac "x dvd gcd a b")
  apply simp
  apply (erule (1) nat_gcd_greatest)
done

lemma int_coprime_common_divisor: "coprime (a::int) b \<Longrightarrow> x dvd a \<Longrightarrow>
    x dvd b \<Longrightarrow> abs x = 1"
  apply (subgoal_tac "x dvd gcd a b")
  apply simp
  apply (erule (1) int_gcd_greatest)
done

lemma nat_coprime_divisors: "(d::int) dvd a \<Longrightarrow> e dvd b \<Longrightarrow> coprime a b \<Longrightarrow>
    coprime d e"
  apply (auto simp add: dvd_def)
  apply (frule int_coprime_lmult)
  apply (subst int_gcd_commute)
  apply (subst (asm) (2) int_gcd_commute)
  apply (erule int_coprime_lmult)
done

lemma nat_invertible_coprime: "(x::nat) * y mod m = 1 \<Longrightarrow> coprime x m"
apply (metis nat_coprime_lmult nat_gcd_1 nat_gcd_commute nat_gcd_red)
done

lemma int_invertible_coprime: "(x::int) * y mod m = 1 \<Longrightarrow> coprime x m"
apply (metis int_coprime_lmult int_gcd_1 int_gcd_commute int_gcd_red)
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
proof (induct x y rule: nat_gcd_induct)
  fix m :: nat
  show "fst (bezw m 0) * int m + snd (bezw m 0) * int 0 = int (gcd m 0)"
    by auto
  next fix m :: nat and n
    assume ngt0: "n > 0" and
      ih: "fst (bezw n (m mod n)) * int n +
        snd (bezw n (m mod n)) * int (m mod n) =
        int (gcd n (m mod n))"
    thus "fst (bezw m n) * int m + snd (bezw m n) * int n = int (gcd m n)"
      apply (simp add: bezw_non_0 nat_gcd_non_0)
      apply (erule subst)
      apply (simp add: ring_simps)
      apply (subst mod_div_equality [of m n, symmetric])
      (* applying simp here undoes the last substitution!
         what is procedure cancel_div_mod? *)
      apply (simp only: ring_simps zadd_int [symmetric]
        zmult_int [symmetric])
      done
qed

lemma int_bezout:
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
    apply (subst int_gcd_neg2 [symmetric])
    apply auto
    done
  moreover have "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of "-x" y])
    apply auto
    apply (rule_tac x = "-u" in exI)
    apply (rule_tac x = v in exI)
    apply (subst int_gcd_neg1 [symmetric])
    apply auto
    done
  moreover have "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of "-x" "-y"])
    apply auto
    apply (rule_tac x = "-u" in exI)
    apply (rule_tac x = "-v" in exI)
    apply (subst int_gcd_neg1 [symmetric])
    apply (subst int_gcd_neg2 [symmetric])
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

lemma nat_bezout_lemma:
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

lemma nat_bezout_add: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
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

lemma nat_bezout1: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x - b * y = d \<or> b * x - a * y = d)"
  using nat_bezout_add[of a b]
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="y" in exI)
  apply auto
done

lemma nat_bezout_add_strong: assumes nz: "a \<noteq> (0::nat)"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
proof-
 from nz have ap: "a > 0" by simp
 from nat_bezout_add[of a b]
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

lemma nat_bezout: assumes a: "(a::nat) \<noteq> 0"
  shows "\<exists>x y. a * x = b * y + gcd a b"
proof-
  let ?g = "gcd a b"
  from nat_bezout_add_strong[OF a, of b]
  obtain d x y where d: "d dvd a" "d dvd b" "a * x = b * y + d" by blast
  from d(1,2) have "d dvd ?g" by simp
  then obtain k where k: "?g = d*k" unfolding dvd_def by blast
  from d(3) have "a * x * k = (b * y + d) *k " by auto
  hence "a * (x * k) = b * (y*k) + ?g" by (algebra add: k)
  thus ?thesis by blast
qed


subsection {* LCM *}

lemma int_lcm_altdef: "lcm (a::int) b = (abs a) * (abs b) div gcd a b"
  by (simp add: lcm_int_def lcm_nat_def zdiv_int
    zmult_int [symmetric] gcd_int_def)

lemma nat_prod_gcd_lcm: "(m::nat) * n = gcd m n * lcm m n"
  unfolding lcm_nat_def
  by (simp add: dvd_mult_div_cancel [OF nat_gcd_dvd_prod])

lemma int_prod_gcd_lcm: "abs(m::int) * abs n = gcd m n * lcm m n"
  unfolding lcm_int_def gcd_int_def
  apply (subst int_mult [symmetric])
  apply (subst nat_prod_gcd_lcm [symmetric])
  apply (subst nat_abs_mult_distrib [symmetric])
  apply (simp, simp add: abs_mult)
done

lemma nat_lcm_0 [simp]: "lcm (m::nat) 0 = 0"
  unfolding lcm_nat_def by simp

lemma int_lcm_0 [simp]: "lcm (m::int) 0 = 0"
  unfolding lcm_int_def by simp

lemma nat_lcm_1 [simp]: "lcm (m::nat) 1 = m"
  unfolding lcm_nat_def by simp

lemma nat_lcm_Suc_0 [simp]: "lcm (m::nat) (Suc 0) = m"
  unfolding lcm_nat_def by (simp add: One_nat_def)

lemma int_lcm_1 [simp]: "lcm (m::int) 1 = abs m"
  unfolding lcm_int_def by simp

lemma nat_lcm_0_left [simp]: "lcm (0::nat) n = 0"
  unfolding lcm_nat_def by simp

lemma int_lcm_0_left [simp]: "lcm (0::int) n = 0"
  unfolding lcm_int_def by simp

lemma nat_lcm_1_left [simp]: "lcm (1::nat) m = m"
  unfolding lcm_nat_def by simp

lemma nat_lcm_Suc_0_left [simp]: "lcm (Suc 0) m = m"
  unfolding lcm_nat_def by (simp add: One_nat_def)

lemma int_lcm_1_left [simp]: "lcm (1::int) m = abs m"
  unfolding lcm_int_def by simp

lemma nat_lcm_commute: "lcm (m::nat) n = lcm n m"
  unfolding lcm_nat_def by (simp add: nat_gcd_commute ring_simps)

lemma int_lcm_commute: "lcm (m::int) n = lcm n m"
  unfolding lcm_int_def by (subst nat_lcm_commute, rule refl)


lemma nat_lcm_pos:
  assumes mpos: "(m::nat) > 0"
  and npos: "n>0"
  shows "lcm m n > 0"
proof(rule ccontr, simp add: lcm_nat_def nat_gcd_zero)
  assume h:"m*n div gcd m n = 0"
  from mpos npos have "gcd m n \<noteq> 0" using nat_gcd_zero by simp
  hence gcdp: "gcd m n > 0" by simp
  with h
  have "m*n < gcd m n"
    by (cases "m * n < gcd m n")
       (auto simp add: div_if[OF gcdp, where m="m*n"])
  moreover
  have "gcd m n dvd m" by simp
  with mpos dvd_imp_le have t1:"gcd m n \<le> m" by simp
  with npos have t1:"gcd m n*n \<le> m*n" by simp
  have "gcd m n \<le> gcd m n*n" using npos by simp
  with t1 have "gcd m n \<le> m*n" by arith
  ultimately show "False" by simp
qed

lemma int_lcm_pos:
  assumes mneq0: "(m::int) ~= 0"
  and npos: "n ~= 0"
  shows "lcm m n > 0"

  apply (subst int_lcm_abs)
  apply (rule nat_lcm_pos [transferred])
  using prems apply auto
done

lemma nat_dvd_pos:
  fixes n m :: nat
  assumes "n > 0" and "m dvd n"
  shows "m > 0"
using assms by (cases m) auto

lemma nat_lcm_least:
  assumes "(m::nat) dvd k" and "n dvd k"
  shows "lcm m n dvd k"
proof (cases k)
  case 0 then show ?thesis by auto
next
  case (Suc _) then have pos_k: "k > 0" by auto
  from assms nat_dvd_pos [OF this] have pos_mn: "m > 0" "n > 0" by auto
  with nat_gcd_zero [of m n] have pos_gcd: "gcd m n > 0" by simp
  from assms obtain p where k_m: "k = m * p" using dvd_def by blast
  from assms obtain q where k_n: "k = n * q" using dvd_def by blast
  from pos_k k_m have pos_p: "p > 0" by auto
  from pos_k k_n have pos_q: "q > 0" by auto
  have "k * k * gcd q p = k * gcd (k * q) (k * p)"
    by (simp add: mult_ac nat_gcd_mult_distrib)
  also have "\<dots> = k * gcd (m * p * q) (n * q * p)"
    by (simp add: k_m [symmetric] k_n [symmetric])
  also have "\<dots> = k * p * q * gcd m n"
    by (simp add: mult_ac nat_gcd_mult_distrib)
  finally have "(m * p) * (n * q) * gcd q p = k * p * q * gcd m n"
    by (simp only: k_m [symmetric] k_n [symmetric])
  then have "p * q * m * n * gcd q p = p * q * k * gcd m n"
    by (simp add: mult_ac)
  with pos_p pos_q have "m * n * gcd q p = k * gcd m n"
    by simp
  with nat_prod_gcd_lcm [of m n]
  have "lcm m n * gcd q p * gcd m n = k * gcd m n"
    by (simp add: mult_ac)
  with pos_gcd have "lcm m n * gcd q p = k" by auto
  then show ?thesis using dvd_def by auto
qed

lemma int_lcm_least:
  assumes "(m::int) dvd k" and "n dvd k"
  shows "lcm m n dvd k"

  apply (subst int_lcm_abs)
  apply (rule dvd_trans)
  apply (rule nat_lcm_least [transferred, of _ "abs k" _])
  using prems apply auto
done

lemma nat_lcm_dvd1: "(m::nat) dvd lcm m n"
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
    also have "\<dots> = m * k" using mpos npos nat_gcd_zero by simp
    finally show ?thesis by (simp add: lcm_nat_def)
  qed
qed

lemma int_lcm_dvd1: "(m::int) dvd lcm m n"
  apply (subst int_lcm_abs)
  apply (rule dvd_trans)
  prefer 2
  apply (rule nat_lcm_dvd1 [transferred])
  apply auto
done

lemma nat_lcm_dvd2: "(n::nat) dvd lcm m n"
  by (subst nat_lcm_commute, rule nat_lcm_dvd1)

lemma int_lcm_dvd2: "(n::int) dvd lcm m n"
  by (subst int_lcm_commute, rule int_lcm_dvd1)

lemma dvd_lcm_I1_nat[simp]: "(k::nat) dvd m \<Longrightarrow> k dvd lcm m n"
by(metis nat_lcm_dvd1 dvd_trans)

lemma dvd_lcm_I2_nat[simp]: "(k::nat) dvd n \<Longrightarrow> k dvd lcm m n"
by(metis nat_lcm_dvd2 dvd_trans)

lemma dvd_lcm_I1_int[simp]: "(i::int) dvd m \<Longrightarrow> i dvd lcm m n"
by(metis int_lcm_dvd1 dvd_trans)

lemma dvd_lcm_I2_int[simp]: "(i::int) dvd n \<Longrightarrow> i dvd lcm m n"
by(metis int_lcm_dvd2 dvd_trans)

lemma nat_lcm_unique: "(a::nat) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (auto intro: dvd_anti_sym nat_lcm_least nat_lcm_dvd1 nat_lcm_dvd2)

lemma int_lcm_unique: "d >= 0 \<and> (a::int) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (auto intro: dvd_anti_sym [transferred] int_lcm_least)

lemma nat_lcm_dvd_eq [simp]: "(x::nat) dvd y \<Longrightarrow> lcm x y = y"
  apply (rule sym)
  apply (subst nat_lcm_unique [symmetric])
  apply auto
done

lemma int_lcm_dvd_eq [simp]: "0 <= y \<Longrightarrow> (x::int) dvd y \<Longrightarrow> lcm x y = y"
  apply (rule sym)
  apply (subst int_lcm_unique [symmetric])
  apply auto
done

lemma nat_lcm_dvd_eq' [simp]: "(x::nat) dvd y \<Longrightarrow> lcm y x = y"
  by (subst nat_lcm_commute, erule nat_lcm_dvd_eq)

lemma int_lcm_dvd_eq' [simp]: "y >= 0 \<Longrightarrow> (x::int) dvd y \<Longrightarrow> lcm y x = y"
  by (subst int_lcm_commute, erule (1) int_lcm_dvd_eq)


lemma lcm_assoc_nat: "lcm (lcm n m) (p::nat) = lcm n (lcm m p)"
apply(rule nat_lcm_unique[THEN iffD1])
apply (metis dvd.order_trans nat_lcm_unique)
done

lemma lcm_assoc_int: "lcm (lcm n m) (p::int) = lcm n (lcm m p)"
apply(rule int_lcm_unique[THEN iffD1])
apply (metis dvd_trans int_lcm_unique)
done

lemmas lcm_left_commute_nat =
  mk_left_commute[of lcm, OF lcm_assoc_nat nat_lcm_commute]

lemmas lcm_left_commute_int =
  mk_left_commute[of lcm, OF lcm_assoc_int int_lcm_commute]

lemmas lcm_ac_nat = lcm_assoc_nat nat_lcm_commute lcm_left_commute_nat
lemmas lcm_ac_int = lcm_assoc_int int_lcm_commute lcm_left_commute_int


subsection {* Primes *}

(* Is there a better way to handle these, rather than making them
   elim rules? *)

lemma nat_prime_ge_0 [elim]: "prime (p::nat) \<Longrightarrow> p >= 0"
  by (unfold prime_nat_def, auto)

lemma nat_prime_gt_0 [elim]: "prime (p::nat) \<Longrightarrow> p > 0"
  by (unfold prime_nat_def, auto)

lemma nat_prime_ge_1 [elim]: "prime (p::nat) \<Longrightarrow> p >= 1"
  by (unfold prime_nat_def, auto)

lemma nat_prime_gt_1 [elim]: "prime (p::nat) \<Longrightarrow> p > 1"
  by (unfold prime_nat_def, auto)

lemma nat_prime_ge_Suc_0 [elim]: "prime (p::nat) \<Longrightarrow> p >= Suc 0"
  by (unfold prime_nat_def, auto)

lemma nat_prime_gt_Suc_0 [elim]: "prime (p::nat) \<Longrightarrow> p > Suc 0"
  by (unfold prime_nat_def, auto)

lemma nat_prime_ge_2 [elim]: "prime (p::nat) \<Longrightarrow> p >= 2"
  by (unfold prime_nat_def, auto)

lemma int_prime_ge_0 [elim]: "prime (p::int) \<Longrightarrow> p >= 0"
  by (unfold prime_int_def prime_nat_def, auto)

lemma int_prime_gt_0 [elim]: "prime (p::int) \<Longrightarrow> p > 0"
  by (unfold prime_int_def prime_nat_def, auto)

lemma int_prime_ge_1 [elim]: "prime (p::int) \<Longrightarrow> p >= 1"
  by (unfold prime_int_def prime_nat_def, auto)

lemma int_prime_gt_1 [elim]: "prime (p::int) \<Longrightarrow> p > 1"
  by (unfold prime_int_def prime_nat_def, auto)

lemma int_prime_ge_2 [elim]: "prime (p::int) \<Longrightarrow> p >= 2"
  by (unfold prime_int_def prime_nat_def, auto)

thm prime_nat_def;
thm prime_nat_def [transferred];

lemma prime_int_altdef: "prime (p::int) = (1 < p \<and> (\<forall>m \<ge> 0. m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  using prime_nat_def [transferred]
    apply (case_tac "p >= 0")
    by (blast, auto simp add: int_prime_ge_0)

(* To do: determine primality of any numeral *)

lemma nat_zero_not_prime [simp]: "~prime (0::nat)"
  by (simp add: prime_nat_def)

lemma int_zero_not_prime [simp]: "~prime (0::int)"
  by (simp add: prime_int_def)

lemma nat_one_not_prime [simp]: "~prime (1::nat)"
  by (simp add: prime_nat_def)

lemma nat_Suc_0_not_prime [simp]: "~prime (Suc 0)"
  by (simp add: prime_nat_def One_nat_def)

lemma int_one_not_prime [simp]: "~prime (1::int)"
  by (simp add: prime_int_def)

lemma nat_two_is_prime [simp]: "prime (2::nat)"
  apply (auto simp add: prime_nat_def)
  apply (case_tac m)
  apply (auto dest!: dvd_imp_le)
  done

lemma int_two_is_prime [simp]: "prime (2::int)"
  by (rule nat_two_is_prime [transferred direction: nat "op <= (0::int)"])

lemma nat_prime_imp_coprime: "prime (p::nat) \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_nat_def)
  apply (metis nat_gcd_dvd1 nat_gcd_dvd2)
  done

lemma int_prime_imp_coprime: "prime (p::int) \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_int_altdef)
  apply (metis int_gcd_dvd1 int_gcd_dvd2 int_gcd_ge_0)
  done

lemma nat_prime_dvd_mult: "prime (p::nat) \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: nat_coprime_dvd_mult nat_prime_imp_coprime)

lemma int_prime_dvd_mult: "prime (p::int) \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: int_coprime_dvd_mult int_prime_imp_coprime)

lemma nat_prime_dvd_mult_eq [simp]: "prime (p::nat) \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule nat_prime_dvd_mult, auto)

lemma int_prime_dvd_mult_eq [simp]: "prime (p::int) \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule int_prime_dvd_mult, auto)

lemma nat_not_prime_eq_prod: "(n::nat) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_nat_def dvd_def apply auto
  apply (subgoal_tac "k > 1")
  apply force
  apply (subgoal_tac "k ~= 0")
  apply force
  apply (rule notI)
  apply force
done

(* there's a lot of messing around with signs of products here --
   could this be made more automatic? *)
lemma int_not_prime_eq_prod: "(n::int) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_int_altdef dvd_def
  apply auto
  apply (rule_tac x = m in exI)
  apply (rule_tac x = k in exI)
  apply (auto simp add: mult_compare_simps)
  apply (subgoal_tac "k > 0")
  apply arith
  apply (case_tac "k <= 0")
  apply (subgoal_tac "m * k <= 0")
  apply force
  apply (subst zero_compare_simps(8))
  apply auto
  apply (subgoal_tac "m * k <= 0")
  apply force
  apply (subst zero_compare_simps(8))
  apply auto
done

lemma nat_prime_dvd_power [rule_format]: "prime (p::nat) -->
    n > 0 --> (p dvd x^n --> p dvd x)"
  by (induct n rule: nat_induct, auto)

lemma int_prime_dvd_power [rule_format]: "prime (p::int) -->
    n > 0 --> (p dvd x^n --> p dvd x)"
  apply (induct n rule: nat_induct, auto)
  apply (frule int_prime_ge_0)
  apply auto
done

lemma nat_prime_imp_power_coprime: "prime (p::nat) \<Longrightarrow> ~ p dvd a \<Longrightarrow>
    coprime a (p^m)"
  apply (rule nat_coprime_exp)
  apply (subst nat_gcd_commute)
  apply (erule (1) nat_prime_imp_coprime)
done

lemma int_prime_imp_power_coprime: "prime (p::int) \<Longrightarrow> ~ p dvd a \<Longrightarrow>
    coprime a (p^m)"
  apply (rule int_coprime_exp)
  apply (subst int_gcd_commute)
  apply (erule (1) int_prime_imp_coprime)
done

lemma nat_primes_coprime: "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  apply (rule nat_prime_imp_coprime, assumption)
  apply (unfold prime_nat_def, auto)
done

lemma int_primes_coprime: "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  apply (rule int_prime_imp_coprime, assumption)
  apply (unfold prime_int_altdef, clarify)
  apply (drule_tac x = q in spec)
  apply (drule_tac x = p in spec)
  apply auto
done

lemma nat_primes_imp_powers_coprime: "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow>
    coprime (p^m) (q^n)"
  by (rule nat_coprime_exp2, rule nat_primes_coprime)

lemma int_primes_imp_powers_coprime: "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow>
    coprime (p^m) (q^n)"
  by (rule int_coprime_exp2, rule int_primes_coprime)

lemma nat_prime_factor: "n \<noteq> (1::nat) \<Longrightarrow> \<exists> p. prime p \<and> p dvd n"
  apply (induct n rule: nat_less_induct)
  apply (case_tac "n = 0")
  using nat_two_is_prime apply blast
  apply (case_tac "prime n")
  apply blast
  apply (subgoal_tac "n > 1")
  apply (frule (1) nat_not_prime_eq_prod)
  apply (auto intro: dvd_mult dvd_mult2)
done

(* An Isar version:

lemma nat_prime_factor_b:
  fixes n :: nat
  assumes "n \<noteq> 1"
  shows "\<exists>p. prime p \<and> p dvd n"

using `n ~= 1`
proof (induct n rule: nat_less_induct)
  fix n :: nat
  assume "n ~= 1" and
    ih: "\<forall>m<n. m \<noteq> 1 \<longrightarrow> (\<exists>p. prime p \<and> p dvd m)"
  thus "\<exists>p. prime p \<and> p dvd n"
  proof -
  {
    assume "n = 0"
    moreover note nat_two_is_prime
    ultimately have ?thesis
      by (auto simp del: nat_two_is_prime)
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
    with `~ prime n` and nat_not_prime_eq_prod obtain m k where
      "n = m * k" and "1 < m" and "m < n" by blast
    with ih obtain p where "prime p" and "p dvd m" by blast
    with `n = m * k` have ?thesis by auto
  }
  ultimately show ?thesis by blast
  qed
qed

*)

text {* One property of coprimality is easier to prove via prime factors. *}

lemma nat_prime_divprod_pow:
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
    from nat_prime_dvd_mult[OF p pab']
    have "p dvd a \<or> p dvd b" .
    moreover
    {assume pa: "p dvd a"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
      from nat_coprime_common_divisor [OF ab, OF pa] p have "\<not> p dvd b" by auto
      with p have "coprime b p"
        by (subst nat_gcd_commute, intro nat_prime_imp_coprime)
      hence pnb: "coprime (p^n) b"
        by (subst nat_gcd_commute, rule nat_coprime_exp)
      from nat_coprime_divprod[OF pnba pnb] have ?thesis by blast }
    moreover
    {assume pb: "p dvd b"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
      from nat_coprime_common_divisor [OF ab, of p] pb p have "\<not> p dvd a"
        by auto
      with p have "coprime a p"
        by (subst nat_gcd_commute, intro nat_prime_imp_coprime)
      hence pna: "coprime (p^n) a"
        by (subst nat_gcd_commute, rule nat_coprime_exp)
      from nat_coprime_divprod[OF pab pna] have ?thesis by blast }
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

end
