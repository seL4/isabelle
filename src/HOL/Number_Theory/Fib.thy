(*  Title:      Fib.thy
    Authors:    Lawrence C. Paulson, Jeremy Avigad


Defines the fibonacci function.

The original "Fib" is due to Lawrence C. Paulson, and was adapted by
Jeremy Avigad.
*)


header {* Fib *}

theory Fib
imports Binomial
begin


subsection {* Main definitions *}

class fib =

fixes 
  fib :: "'a \<Rightarrow> 'a"


(* definition for the natural numbers *)

instantiation nat :: fib

begin 

fun 
  fib_nat :: "nat \<Rightarrow> nat"
where
  "fib_nat n =
   (if n = 0 then 0 else
   (if n = 1 then 1 else
     fib (n - 1) + fib (n - 2)))"

instance proof qed

end

(* definition for the integers *)

instantiation int :: fib

begin 

definition
  fib_int :: "int \<Rightarrow> int"
where  
  "fib_int n = (if n >= 0 then int (fib (nat n)) else 0)"

instance proof qed

end


subsection {* Set up Transfer *}


lemma transfer_nat_int_fib:
  "(x::int) >= 0 \<Longrightarrow> fib (nat x) = nat (fib x)"
  unfolding fib_int_def by auto

lemma transfer_nat_int_fib_closure:
  "n >= (0::int) \<Longrightarrow> fib n >= 0"
  by (auto simp add: fib_int_def)

declare TransferMorphism_nat_int[transfer add return: 
    transfer_nat_int_fib transfer_nat_int_fib_closure]

lemma transfer_int_nat_fib:
  "fib (int n) = int (fib n)"
  unfolding fib_int_def by auto

lemma transfer_int_nat_fib_closure:
  "is_nat n \<Longrightarrow> fib n >= 0"
  unfolding fib_int_def by auto

declare TransferMorphism_int_nat[transfer add return: 
    transfer_int_nat_fib transfer_int_nat_fib_closure]


subsection {* Fibonacci numbers *}

lemma fib_0_nat [simp]: "fib (0::nat) = 0"
  by simp

lemma fib_0_int [simp]: "fib (0::int) = 0"
  unfolding fib_int_def by simp

lemma fib_1_nat [simp]: "fib (1::nat) = 1"
  by simp

lemma fib_Suc_0_nat [simp]: "fib (Suc 0) = Suc 0"
  by simp

lemma fib_1_int [simp]: "fib (1::int) = 1"
  unfolding fib_int_def by simp

lemma fib_reduce_nat: "(n::nat) >= 2 \<Longrightarrow> fib n = fib (n - 1) + fib (n - 2)"
  by simp

declare fib_nat.simps [simp del]

lemma fib_reduce_int: "(n::int) >= 2 \<Longrightarrow> fib n = fib (n - 1) + fib (n - 2)"
  unfolding fib_int_def
  by (auto simp add: fib_reduce_nat nat_diff_distrib)

lemma fib_neg_int [simp]: "(n::int) < 0 \<Longrightarrow> fib n = 0"
  unfolding fib_int_def by auto

lemma fib_2_nat [simp]: "fib (2::nat) = 1"
  by (subst fib_reduce_nat, auto)

lemma fib_2_int [simp]: "fib (2::int) = 1"
  by (subst fib_reduce_int, auto)

lemma fib_plus_2_nat: "fib ((n::nat) + 2) = fib (n + 1) + fib n"
  by (subst fib_reduce_nat, auto simp add: One_nat_def)
(* the need for One_nat_def is due to the natdiff_cancel_numerals
   procedure *)

lemma fib_induct_nat: "P (0::nat) \<Longrightarrow> P (1::nat) \<Longrightarrow> 
    (!!n. P n \<Longrightarrow> P (n + 1) \<Longrightarrow> P (n + 2)) \<Longrightarrow> P n"
  apply (atomize, induct n rule: nat_less_induct)
  apply auto
  apply (case_tac "n = 0", force)
  apply (case_tac "n = 1", force)
  apply (subgoal_tac "n >= 2")
  apply (frule_tac x = "n - 1" in spec)
  apply (drule_tac x = "n - 2" in spec)
  apply (drule_tac x = "n - 2" in spec)
  apply auto
  apply (auto simp add: One_nat_def) (* again, natdiff_cancel *)
done

lemma fib_add_nat: "fib ((n::nat) + k + 1) = fib (k + 1) * fib (n + 1) + 
    fib k * fib n"
  apply (induct n rule: fib_induct_nat)
  apply auto
  apply (subst fib_reduce_nat)
  apply (auto simp add: ring_simps)
  apply (subst (1 3 5) fib_reduce_nat)
  apply (auto simp add: ring_simps Suc_eq_plus1)
(* hmmm. Why doesn't "n + (1 + (1 + k))" simplify to "n + k + 2"? *)
  apply (subgoal_tac "n + (k + 2) = n + (1 + (1 + k))")
  apply (erule ssubst) back back
  apply (erule ssubst) back 
  apply auto
done

lemma fib_add'_nat: "fib (n + Suc k) = fib (Suc k) * fib (Suc n) + 
    fib k * fib n"
  using fib_add_nat by (auto simp add: One_nat_def)


(* transfer from nats to ints *)
lemma fib_add_int [rule_format]: "(n::int) >= 0 \<Longrightarrow> k >= 0 \<Longrightarrow>
    fib (n + k + 1) = fib (k + 1) * fib (n + 1) + 
    fib k * fib n "

  by (rule fib_add_nat [transferred])

lemma fib_neq_0_nat: "(n::nat) > 0 \<Longrightarrow> fib n ~= 0"
  apply (induct n rule: fib_induct_nat)
  apply (auto simp add: fib_plus_2_nat)
done

lemma fib_gr_0_nat: "(n::nat) > 0 \<Longrightarrow> fib n > 0"
  by (frule fib_neq_0_nat, simp)

lemma fib_gr_0_int: "(n::int) > 0 \<Longrightarrow> fib n > 0"
  unfolding fib_int_def by (simp add: fib_gr_0_nat)

text {*
  \medskip Concrete Mathematics, page 278: Cassini's identity.  The proof is
  much easier using integers, not natural numbers!
*}

lemma fib_Cassini_aux_int: "fib (int n + 2) * fib (int n) - 
    (fib (int n + 1))^2 = (-1)^(n + 1)"
  apply (induct n)
  apply (auto simp add: ring_simps power2_eq_square fib_reduce_int
      power_add)
done

lemma fib_Cassini_int: "n >= 0 \<Longrightarrow> fib (n + 2) * fib n - 
    (fib (n + 1))^2 = (-1)^(nat n + 1)"
  by (insert fib_Cassini_aux_int [of "nat n"], auto)

(*
lemma fib_Cassini'_int: "n >= 0 \<Longrightarrow> fib (n + 2) * fib n = 
    (fib (n + 1))^2 + (-1)^(nat n + 1)"
  by (frule fib_Cassini_int, simp) 
*)

lemma fib_Cassini'_int: "n >= 0 \<Longrightarrow> fib ((n::int) + 2) * fib n =
  (if even n then tsub ((fib (n + 1))^2) 1
   else (fib (n + 1))^2 + 1)"
  apply (frule fib_Cassini_int, auto simp add: pos_int_even_equiv_nat_even)
  apply (subst tsub_eq)
  apply (insert fib_gr_0_int [of "n + 1"], force)
  apply auto
done

lemma fib_Cassini_nat: "fib ((n::nat) + 2) * fib n =
  (if even n then (fib (n + 1))^2 - 1
   else (fib (n + 1))^2 + 1)"

  by (rule fib_Cassini'_int [transferred, of n], auto)


text {* \medskip Toward Law 6.111 of Concrete Mathematics *}

lemma coprime_fib_plus_1_nat: "coprime (fib (n::nat)) (fib (n + 1))"
  apply (induct n rule: fib_induct_nat)
  apply auto
  apply (subst (2) fib_reduce_nat)
  apply (auto simp add: Suc_eq_plus1) (* again, natdiff_cancel *)
  apply (subst add_commute, auto)
  apply (subst gcd_commute_nat, auto simp add: ring_simps)
done

lemma coprime_fib_Suc_nat: "coprime (fib n) (fib (Suc n))"
  using coprime_fib_plus_1_nat by (simp add: One_nat_def)

lemma coprime_fib_plus_1_int: 
    "n >= 0 \<Longrightarrow> coprime (fib (n::int)) (fib (n + 1))"
  by (erule coprime_fib_plus_1_nat [transferred])

lemma gcd_fib_add_nat: "gcd (fib (m::nat)) (fib (n + m)) = gcd (fib m) (fib n)"
  apply (simp add: gcd_commute_nat [of "fib m"])
  apply (rule cases_nat [of _ m])
  apply simp
  apply (subst add_assoc [symmetric])
  apply (simp add: fib_add_nat)
  apply (subst gcd_commute_nat)
  apply (subst mult_commute)
  apply (subst gcd_add_mult_nat)
  apply (subst gcd_commute_nat)
  apply (rule gcd_mult_cancel_nat)
  apply (rule coprime_fib_plus_1_nat)
done

lemma gcd_fib_add_int [rule_format]: "m >= 0 \<Longrightarrow> n >= 0 \<Longrightarrow> 
    gcd (fib (m::int)) (fib (n + m)) = gcd (fib m) (fib n)"
  by (erule gcd_fib_add_nat [transferred])

lemma gcd_fib_diff_nat: "(m::nat) \<le> n \<Longrightarrow> 
    gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: gcd_fib_add_nat [symmetric, of _ "n-m"])

lemma gcd_fib_diff_int: "0 <= (m::int) \<Longrightarrow> m \<le> n \<Longrightarrow> 
    gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: gcd_fib_add_int [symmetric, of _ "n-m"])

lemma gcd_fib_mod_nat: "0 < (m::nat) \<Longrightarrow> 
    gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
proof (induct n rule: less_induct)
  case (less n)
  from less.prems have pos_m: "0 < m" .
  show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
  proof (cases "m < n")
    case True note m_n = True
    then have m_n': "m \<le> n" by auto
    with pos_m have pos_n: "0 < n" by auto
    with pos_m m_n have diff: "n - m < n" by auto
    have "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib ((n - m) mod m))"
    by (simp add: mod_if [of n]) (insert m_n, auto)
    also have "\<dots> = gcd (fib m)  (fib (n - m))" 
      by (simp add: less.hyps diff pos_m)
    also have "\<dots> = gcd (fib m) (fib n)" by (simp add: gcd_fib_diff_nat m_n')
    finally show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" .
  next
    case False then show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
    by (cases "m = n") auto
  qed
qed

lemma gcd_fib_mod_int: 
  assumes "0 < (m::int)" and "0 <= n"
  shows "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"

  apply (rule gcd_fib_mod_nat [transferred])
  using prems apply auto
done

lemma fib_gcd_nat: "fib (gcd (m::nat) n) = gcd (fib m) (fib n)"  
    -- {* Law 6.111 *}
  apply (induct m n rule: gcd_nat_induct)
  apply (simp_all add: gcd_non_0_nat gcd_commute_nat gcd_fib_mod_nat)
done

lemma fib_gcd_int: "m >= 0 \<Longrightarrow> n >= 0 \<Longrightarrow>
    fib (gcd (m::int) n) = gcd (fib m) (fib n)"
  by (erule fib_gcd_nat [transferred])

lemma atMost_plus_one_nat: "{..(k::nat) + 1} = insert (k + 1) {..k}" 
  by auto

theorem fib_mult_eq_setsum_nat:
    "fib ((n::nat) + 1) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  apply (induct n)
  apply (auto simp add: atMost_plus_one_nat fib_plus_2_nat ring_simps)
done

theorem fib_mult_eq_setsum'_nat:
    "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  using fib_mult_eq_setsum_nat by (simp add: One_nat_def)

theorem fib_mult_eq_setsum_int [rule_format]:
    "n >= 0 \<Longrightarrow> fib ((n::int) + 1) * fib n = (\<Sum>k \<in> {0..n}. fib k * fib k)"
  by (erule fib_mult_eq_setsum_nat [transferred])

end
