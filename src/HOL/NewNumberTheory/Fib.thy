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

lemma nat_fib_0 [simp]: "fib (0::nat) = 0"
  by simp

lemma int_fib_0 [simp]: "fib (0::int) = 0"
  unfolding fib_int_def by simp

lemma nat_fib_1 [simp]: "fib (1::nat) = 1"
  by simp

lemma nat_fib_Suc_0 [simp]: "fib (Suc 0) = Suc 0"
  by simp

lemma int_fib_1 [simp]: "fib (1::int) = 1"
  unfolding fib_int_def by simp

lemma nat_fib_reduce: "(n::nat) >= 2 \<Longrightarrow> fib n = fib (n - 1) + fib (n - 2)"
  by simp

declare fib_nat.simps [simp del]

lemma int_fib_reduce: "(n::int) >= 2 \<Longrightarrow> fib n = fib (n - 1) + fib (n - 2)"
  unfolding fib_int_def
  by (auto simp add: nat_fib_reduce nat_diff_distrib)

lemma int_fib_neg [simp]: "(n::int) < 0 \<Longrightarrow> fib n = 0"
  unfolding fib_int_def by auto

lemma nat_fib_2 [simp]: "fib (2::nat) = 1"
  by (subst nat_fib_reduce, auto)

lemma int_fib_2 [simp]: "fib (2::int) = 1"
  by (subst int_fib_reduce, auto)

lemma nat_fib_plus_2: "fib ((n::nat) + 2) = fib (n + 1) + fib n"
  by (subst nat_fib_reduce, auto simp add: One_nat_def)
(* the need for One_nat_def is due to the natdiff_cancel_numerals
   procedure *)

lemma nat_fib_induct: "P (0::nat) \<Longrightarrow> P (1::nat) \<Longrightarrow> 
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

lemma nat_fib_add: "fib ((n::nat) + k + 1) = fib (k + 1) * fib (n + 1) + 
    fib k * fib n"
  apply (induct n rule: nat_fib_induct)
  apply auto
  apply (subst nat_fib_reduce)
  apply (auto simp add: ring_simps)
  apply (subst (1 3 5) nat_fib_reduce)
  apply (auto simp add: ring_simps Suc_remove)
(* hmmm. Why doesn't "n + (1 + (1 + k))" simplify to "n + k + 2"? *)
  apply (subgoal_tac "n + (k + 2) = n + (1 + (1 + k))")
  apply (erule ssubst) back back
  apply (erule ssubst) back 
  apply auto
done

lemma nat_fib_add': "fib (n + Suc k) = fib (Suc k) * fib (Suc n) + 
    fib k * fib n"
  using nat_fib_add by (auto simp add: One_nat_def)


(* transfer from nats to ints *)
lemma int_fib_add [rule_format]: "(n::int) >= 0 \<Longrightarrow> k >= 0 \<Longrightarrow>
    fib (n + k + 1) = fib (k + 1) * fib (n + 1) + 
    fib k * fib n "

  by (rule nat_fib_add [transferred])

lemma nat_fib_neq_0: "(n::nat) > 0 \<Longrightarrow> fib n ~= 0"
  apply (induct n rule: nat_fib_induct)
  apply (auto simp add: nat_fib_plus_2)
done

lemma nat_fib_gr_0: "(n::nat) > 0 \<Longrightarrow> fib n > 0"
  by (frule nat_fib_neq_0, simp)

lemma int_fib_gr_0: "(n::int) > 0 \<Longrightarrow> fib n > 0"
  unfolding fib_int_def by (simp add: nat_fib_gr_0)

text {*
  \medskip Concrete Mathematics, page 278: Cassini's identity.  The proof is
  much easier using integers, not natural numbers!
*}

lemma int_fib_Cassini_aux: "fib (int n + 2) * fib (int n) - 
    (fib (int n + 1))^2 = (-1)^(n + 1)"
  apply (induct n)
  apply (auto simp add: ring_simps power2_eq_square int_fib_reduce
      power_add)
done

lemma int_fib_Cassini: "n >= 0 \<Longrightarrow> fib (n + 2) * fib n - 
    (fib (n + 1))^2 = (-1)^(nat n + 1)"
  by (insert int_fib_Cassini_aux [of "nat n"], auto)

(*
lemma int_fib_Cassini': "n >= 0 \<Longrightarrow> fib (n + 2) * fib n = 
    (fib (n + 1))^2 + (-1)^(nat n + 1)"
  by (frule int_fib_Cassini, simp) 
*)

lemma int_fib_Cassini': "n >= 0 \<Longrightarrow> fib ((n::int) + 2) * fib n =
  (if even n then tsub ((fib (n + 1))^2) 1
   else (fib (n + 1))^2 + 1)"
  apply (frule int_fib_Cassini, auto simp add: pos_int_even_equiv_nat_even)
  apply (subst tsub_eq)
  apply (insert int_fib_gr_0 [of "n + 1"], force)
  apply auto
done

lemma nat_fib_Cassini: "fib ((n::nat) + 2) * fib n =
  (if even n then (fib (n + 1))^2 - 1
   else (fib (n + 1))^2 + 1)"

  by (rule int_fib_Cassini' [transferred, of n], auto)


text {* \medskip Toward Law 6.111 of Concrete Mathematics *}

lemma nat_coprime_fib_plus_1: "coprime (fib (n::nat)) (fib (n + 1))"
  apply (induct n rule: nat_fib_induct)
  apply auto
  apply (subst (2) nat_fib_reduce)
  apply (auto simp add: Suc_remove) (* again, natdiff_cancel *)
  apply (subst add_commute, auto)
  apply (subst nat_gcd_commute, auto simp add: ring_simps)
done

lemma nat_coprime_fib_Suc: "coprime (fib n) (fib (Suc n))"
  using nat_coprime_fib_plus_1 by (simp add: One_nat_def)

lemma int_coprime_fib_plus_1: 
    "n >= 0 \<Longrightarrow> coprime (fib (n::int)) (fib (n + 1))"
  by (erule nat_coprime_fib_plus_1 [transferred])

lemma nat_gcd_fib_add: "gcd (fib (m::nat)) (fib (n + m)) = gcd (fib m) (fib n)"
  apply (simp add: nat_gcd_commute [of "fib m"])
  apply (rule nat_cases [of _ m])
  apply simp
  apply (subst add_assoc [symmetric])
  apply (simp add: nat_fib_add)
  apply (subst nat_gcd_commute)
  apply (subst mult_commute)
  apply (subst nat_gcd_add_mult)
  apply (subst nat_gcd_commute)
  apply (rule nat_gcd_mult_cancel)
  apply (rule nat_coprime_fib_plus_1)
done

lemma int_gcd_fib_add [rule_format]: "m >= 0 \<Longrightarrow> n >= 0 \<Longrightarrow> 
    gcd (fib (m::int)) (fib (n + m)) = gcd (fib m) (fib n)"
  by (erule nat_gcd_fib_add [transferred])

lemma nat_gcd_fib_diff: "(m::nat) \<le> n \<Longrightarrow> 
    gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: nat_gcd_fib_add [symmetric, of _ "n-m"])

lemma int_gcd_fib_diff: "0 <= (m::int) \<Longrightarrow> m \<le> n \<Longrightarrow> 
    gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: int_gcd_fib_add [symmetric, of _ "n-m"])

lemma nat_gcd_fib_mod: "0 < (m::nat) \<Longrightarrow> 
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
    also have "\<dots> = gcd (fib m) (fib n)" by (simp add: nat_gcd_fib_diff m_n')
    finally show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" .
  next
    case False then show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
    by (cases "m = n") auto
  qed
qed

lemma int_gcd_fib_mod: 
  assumes "0 < (m::int)" and "0 <= n"
  shows "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"

  apply (rule nat_gcd_fib_mod [transferred])
  using prems apply auto
done

lemma nat_fib_gcd: "fib (gcd (m::nat) n) = gcd (fib m) (fib n)"  
    -- {* Law 6.111 *}
  apply (induct m n rule: nat_gcd_induct)
  apply (simp_all add: nat_gcd_non_0 nat_gcd_commute nat_gcd_fib_mod)
done

lemma int_fib_gcd: "m >= 0 \<Longrightarrow> n >= 0 \<Longrightarrow>
    fib (gcd (m::int) n) = gcd (fib m) (fib n)"
  by (erule nat_fib_gcd [transferred])

lemma nat_atMost_plus_one: "{..(k::nat) + 1} = insert (k + 1) {..k}" 
  by auto

theorem nat_fib_mult_eq_setsum:
    "fib ((n::nat) + 1) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  apply (induct n)
  apply (auto simp add: nat_atMost_plus_one nat_fib_plus_2 ring_simps)
done

theorem nat_fib_mult_eq_setsum':
    "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  using nat_fib_mult_eq_setsum by (simp add: One_nat_def)

theorem int_fib_mult_eq_setsum [rule_format]:
    "n >= 0 \<Longrightarrow> fib ((n::int) + 1) * fib n = (\<Sum>k \<in> {0..n}. fib k * fib k)"
  by (erule nat_fib_mult_eq_setsum [transferred])

end
