(*  Title:      UniqueFactorization.thy
    ID:         
    Author:     Jeremy Avigad

    
    Unique factorization for the natural numbers and the integers.

    Note: there were previous Isabelle formalizations of unique
    factorization due to Thomas Marthedal Rasmussen, and, building on
    that, by Jeremy Avigad and David Gray.  
*)

header {* UniqueFactorization *}

theory UniqueFactorization
imports Cong Multiset
begin

(* inherited from Multiset *)
declare One_nat_def [simp del] 

(* As a simp or intro rule,

     prime p \<Longrightarrow> p > 0

   wreaks havoc here. When the premise includes ALL x :# M. prime x, it 
   leads to the backchaining

     x > 0  
     prime x 
     x :# M   which is, unfortunately,
     count M x > 0
*)


(* useful facts *)

lemma setsum_Un2: "finite (A Un B) \<Longrightarrow> 
    setsum f (A Un B) = setsum f (A - B) + setsum f (B - A) + 
      setsum f (A Int B)"
  apply (subgoal_tac "A Un B = (A - B) Un (B - A) Un (A Int B)")
  apply (erule ssubst)
  apply (subst setsum_Un_disjoint)
  apply auto
  apply (subst setsum_Un_disjoint)
  apply auto
done

lemma setprod_Un2: "finite (A Un B) \<Longrightarrow> 
    setprod f (A Un B) = setprod f (A - B) * setprod f (B - A) * 
      setprod f (A Int B)"
  apply (subgoal_tac "A Un B = (A - B) Un (B - A) Un (A Int B)")
  apply (erule ssubst)
  apply (subst setprod_Un_disjoint)
  apply auto
  apply (subst setprod_Un_disjoint)
  apply auto
done
 
(* Should this go in Multiset.thy? *)
(* TN: No longer an intro-rule; needed only once and might get in the way *)
lemma multiset_eqI: "[| !!x. count M x = count N x |] ==> M = N"
  by (subst multiset_eq_conv_count_eq, blast)

(* Here is a version of set product for multisets. Is it worth moving
   to multiset.thy? If so, one should similarly define msetsum for abelian 
   semirings, using of_nat. Also, is it worth developing bounded quantifiers 
   "ALL i :# M. P i"? 
*)

constdefs
  msetprod :: "('a => ('b::{power,comm_monoid_mult})) => 'a multiset => 'b"
  "msetprod f M == setprod (%x. (f x)^(count M x)) (set_of M)"

syntax
  "_msetprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult" 
      ("(3PROD _:#_. _)" [0, 51, 10] 10)

translations
  "PROD i :# A. b" == "msetprod (%i. b) A"

lemma msetprod_Un: "msetprod f (A+B) = msetprod f A * msetprod f B" 
  apply (simp add: msetprod_def power_add)
  apply (subst setprod_Un2)
  apply auto
  apply (subgoal_tac 
      "(PROD x:set_of A - set_of B. f x ^ count A x * f x ^ count B x) =
       (PROD x:set_of A - set_of B. f x ^ count A x)")
  apply (erule ssubst)
  apply (subgoal_tac 
      "(PROD x:set_of B - set_of A. f x ^ count A x * f x ^ count B x) =
       (PROD x:set_of B - set_of A. f x ^ count B x)")
  apply (erule ssubst)
  apply (subgoal_tac "(PROD x:set_of A. f x ^ count A x) = 
    (PROD x:set_of A - set_of B. f x ^ count A x) *
    (PROD x:set_of A Int set_of B. f x ^ count A x)")
  apply (erule ssubst)
  apply (subgoal_tac "(PROD x:set_of B. f x ^ count B x) = 
    (PROD x:set_of B - set_of A. f x ^ count B x) *
    (PROD x:set_of A Int set_of B. f x ^ count B x)")
  apply (erule ssubst)
  apply (subst setprod_timesf)
  apply (force simp add: mult_ac)
  apply (subst setprod_Un_disjoint [symmetric])
  apply (auto intro: setprod_cong)
  apply (subst setprod_Un_disjoint [symmetric])
  apply (auto intro: setprod_cong)
done


subsection {* unique factorization: multiset version *}

lemma multiset_prime_factorization_exists [rule_format]: "n > 0 --> 
    (EX M. (ALL (p::nat) : set_of M. prime p) & n = (PROD i :# M. i))"
proof (rule nat_less_induct, clarify)
  fix n :: nat
  assume ih: "ALL m < n. 0 < m --> (EX M. (ALL p : set_of M. prime p) & m = 
      (PROD i :# M. i))"
  assume "(n::nat) > 0"
  then have "n = 1 | (n > 1 & prime n) | (n > 1 & ~ prime n)"
    by arith
  moreover 
  {
    assume "n = 1"
    then have "(ALL p : set_of {#}. prime p) & n = (PROD i :# {#}. i)"
        by (auto simp add: msetprod_def)
  } 
  moreover 
  {
    assume "n > 1" and "prime n"
    then have "(ALL p : set_of {# n #}. prime p) & n = (PROD i :# {# n #}. i)"
      by (auto simp add: msetprod_def)
  } 
  moreover 
  {
    assume "n > 1" and "~ prime n"
    from prems not_prime_eq_prod_nat
      obtain m k where "n = m * k & 1 < m & m < n & 1 < k & k < n"
        by blast
    with ih obtain Q R where "(ALL p : set_of Q. prime p) & m = (PROD i:#Q. i)"
        and "(ALL p: set_of R. prime p) & k = (PROD i:#R. i)"
      by blast
    hence "(ALL p: set_of (Q + R). prime p) & n = (PROD i :# Q + R. i)"
      by (auto simp add: prems msetprod_Un set_of_union)
    then have "EX M. (ALL p : set_of M. prime p) & n = (PROD i :# M. i)"..
  }
  ultimately show "EX M. (ALL p : set_of M. prime p) & n = (PROD i::nat:#M. i)"
    by blast
qed

lemma multiset_prime_factorization_unique_aux:
  fixes a :: nat
  assumes "(ALL p : set_of M. prime p)" and
    "(ALL p : set_of N. prime p)" and
    "(PROD i :# M. i) dvd (PROD i:# N. i)"
  shows
    "count M a <= count N a"
proof cases
  assume "a : set_of M"
  with prems have a: "prime a"
    by auto
  with prems have "a ^ count M a dvd (PROD i :# M. i)"
    by (auto intro: dvd_setprod simp add: msetprod_def)
  also have "... dvd (PROD i :# N. i)"
    by (rule prems)
  also have "... = (PROD i : (set_of N). i ^ (count N i))"
    by (simp add: msetprod_def)
  also have "... = 
      a^(count N a) * (PROD i : (set_of N - {a}). i ^ (count N i))"
    proof (cases)
      assume "a : set_of N"
      hence b: "set_of N = {a} Un (set_of N - {a})"
        by auto
      thus ?thesis
        by (subst (1) b, subst setprod_Un_disjoint, auto)
    next
      assume "a ~: set_of N" 
      thus ?thesis
        by auto
    qed
  finally have "a ^ count M a dvd 
      a^(count N a) * (PROD i : (set_of N - {a}). i ^ (count N i))".
  moreover have "coprime (a ^ count M a)
      (PROD i : (set_of N - {a}). i ^ (count N i))"
    apply (subst gcd_commute_nat)
    apply (rule setprod_coprime_nat)
    apply (rule primes_imp_powers_coprime_nat)
    apply (insert prems, auto) 
    done
  ultimately have "a ^ count M a dvd a^(count N a)"
    by (elim coprime_dvd_mult_nat)
  with a show ?thesis 
    by (intro power_dvd_imp_le, auto)
next
  assume "a ~: set_of M"
  thus ?thesis by auto
qed

lemma multiset_prime_factorization_unique:
  assumes "(ALL (p::nat) : set_of M. prime p)" and
    "(ALL p : set_of N. prime p)" and
    "(PROD i :# M. i) = (PROD i:# N. i)"
  shows
    "M = N"
proof -
  {
    fix a
    from prems have "count M a <= count N a"
      by (intro multiset_prime_factorization_unique_aux, auto) 
    moreover from prems have "count N a <= count M a"
      by (intro multiset_prime_factorization_unique_aux, auto) 
    ultimately have "count M a = count N a"
      by auto
  }
  thus ?thesis by (simp add:multiset_eq_conv_count_eq)
qed

constdefs
  multiset_prime_factorization :: "nat => nat multiset"
  "multiset_prime_factorization n ==
     if n > 0 then (THE M. ((ALL p : set_of M. prime p) & 
       n = (PROD i :# M. i)))
     else {#}"

lemma multiset_prime_factorization: "n > 0 ==>
    (ALL p : set_of (multiset_prime_factorization n). prime p) &
       n = (PROD i :# (multiset_prime_factorization n). i)"
  apply (unfold multiset_prime_factorization_def)
  apply clarsimp
  apply (frule multiset_prime_factorization_exists)
  apply clarify
  apply (rule theI)
  apply (insert multiset_prime_factorization_unique, blast)+
done


subsection {* Prime factors and multiplicity for nats and ints *}

class unique_factorization =

fixes
  multiplicity :: "'a \<Rightarrow> 'a \<Rightarrow> nat" and
  prime_factors :: "'a \<Rightarrow> 'a set"

(* definitions for the natural numbers *)

instantiation nat :: unique_factorization

begin

definition
  multiplicity_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "multiplicity_nat p n = count (multiset_prime_factorization n) p"

definition
  prime_factors_nat :: "nat \<Rightarrow> nat set"
where
  "prime_factors_nat n = set_of (multiset_prime_factorization n)"

instance proof qed

end

(* definitions for the integers *)

instantiation int :: unique_factorization

begin

definition
  multiplicity_int :: "int \<Rightarrow> int \<Rightarrow> nat"
where
  "multiplicity_int p n = multiplicity (nat p) (nat n)"

definition
  prime_factors_int :: "int \<Rightarrow> int set"
where
  "prime_factors_int n = int ` (prime_factors (nat n))"

instance proof qed

end


subsection {* Set up transfer *}

lemma transfer_nat_int_prime_factors: 
  "prime_factors (nat n) = nat ` prime_factors n"
  unfolding prime_factors_int_def apply auto
  by (subst transfer_int_nat_set_return_embed, assumption)

lemma transfer_nat_int_prime_factors_closure: "n >= 0 \<Longrightarrow> 
    nat_set (prime_factors n)"
  by (auto simp add: nat_set_def prime_factors_int_def)

lemma transfer_nat_int_multiplicity: "p >= 0 \<Longrightarrow> n >= 0 \<Longrightarrow>
  multiplicity (nat p) (nat n) = multiplicity p n"
  by (auto simp add: multiplicity_int_def)

declare TransferMorphism_nat_int[transfer add return: 
  transfer_nat_int_prime_factors transfer_nat_int_prime_factors_closure
  transfer_nat_int_multiplicity]


lemma transfer_int_nat_prime_factors:
    "prime_factors (int n) = int ` prime_factors n"
  unfolding prime_factors_int_def by auto

lemma transfer_int_nat_prime_factors_closure: "is_nat n \<Longrightarrow> 
    nat_set (prime_factors n)"
  by (simp only: transfer_nat_int_prime_factors_closure is_nat_def)

lemma transfer_int_nat_multiplicity: 
    "multiplicity (int p) (int n) = multiplicity p n"
  by (auto simp add: multiplicity_int_def)

declare TransferMorphism_int_nat[transfer add return: 
  transfer_int_nat_prime_factors transfer_int_nat_prime_factors_closure
  transfer_int_nat_multiplicity]


subsection {* Properties of prime factors and multiplicity for nats and ints *}

lemma prime_factors_ge_0_int [elim]: "p : prime_factors (n::int) \<Longrightarrow> p >= 0"
  by (unfold prime_factors_int_def, auto)

lemma prime_factors_prime_nat [intro]: "p : prime_factors (n::nat) \<Longrightarrow> prime p"
  apply (case_tac "n = 0")
  apply (simp add: prime_factors_nat_def multiset_prime_factorization_def)
  apply (auto simp add: prime_factors_nat_def multiset_prime_factorization)
done

lemma prime_factors_prime_int [intro]:
  assumes "n >= 0" and "p : prime_factors (n::int)"
  shows "prime p"

  apply (rule prime_factors_prime_nat [transferred, of n p])
  using prems apply auto
done

lemma prime_factors_gt_0_nat [elim]: "p : prime_factors x \<Longrightarrow> p > (0::nat)"
  by (frule prime_factors_prime_nat, auto)

lemma prime_factors_gt_0_int [elim]: "x >= 0 \<Longrightarrow> p : prime_factors x \<Longrightarrow> 
    p > (0::int)"
  by (frule (1) prime_factors_prime_int, auto)

lemma prime_factors_finite_nat [iff]: "finite (prime_factors (n::nat))"
  by (unfold prime_factors_nat_def, auto)

lemma prime_factors_finite_int [iff]: "finite (prime_factors (n::int))"
  by (unfold prime_factors_int_def, auto)

lemma prime_factors_altdef_nat: "prime_factors (n::nat) = 
    {p. multiplicity p n > 0}"
  by (force simp add: prime_factors_nat_def multiplicity_nat_def)

lemma prime_factors_altdef_int: "prime_factors (n::int) = 
    {p. p >= 0 & multiplicity p n > 0}"
  apply (unfold prime_factors_int_def multiplicity_int_def)
  apply (subst prime_factors_altdef_nat)
  apply (auto simp add: image_def)
done

lemma prime_factorization_nat: "(n::nat) > 0 \<Longrightarrow> 
    n = (PROD p : prime_factors n. p^(multiplicity p n))"
  by (frule multiset_prime_factorization, 
    simp add: prime_factors_nat_def multiplicity_nat_def msetprod_def)

thm prime_factorization_nat [transferred] 

lemma prime_factorization_int: 
  assumes "(n::int) > 0"
  shows "n = (PROD p : prime_factors n. p^(multiplicity p n))"

  apply (rule prime_factorization_nat [transferred, of n])
  using prems apply auto
done

lemma neq_zero_eq_gt_zero_nat: "((x::nat) ~= 0) = (x > 0)"
  by auto

lemma prime_factorization_unique_nat: 
    "S = { (p::nat) . f p > 0} \<Longrightarrow> finite S \<Longrightarrow> (ALL p : S. prime p) \<Longrightarrow>
      n = (PROD p : S. p^(f p)) \<Longrightarrow>
        S = prime_factors n & (ALL p. f p = multiplicity p n)"
  apply (subgoal_tac "multiset_prime_factorization n = Abs_multiset
      f")
  apply (unfold prime_factors_nat_def multiplicity_nat_def)
  apply (simp add: set_of_def count_def Abs_multiset_inverse multiset_def)
  apply (unfold multiset_prime_factorization_def)
  apply (subgoal_tac "n > 0")
  prefer 2
  apply force
  apply (subst if_P, assumption)
  apply (rule the1_equality)
  apply (rule ex_ex1I)
  apply (rule multiset_prime_factorization_exists, assumption)
  apply (rule multiset_prime_factorization_unique)
  apply force
  apply force
  apply force
  unfolding set_of_def count_def msetprod_def
  apply (subgoal_tac "f : multiset")
  apply (auto simp only: Abs_multiset_inverse)
  unfolding multiset_def apply force 
done

lemma prime_factors_characterization_nat: "S = {p. 0 < f (p::nat)} \<Longrightarrow> 
    finite S \<Longrightarrow> (ALL p:S. prime p) \<Longrightarrow> n = (PROD p:S. p ^ f p) \<Longrightarrow>
      prime_factors n = S"
  by (rule prime_factorization_unique_nat [THEN conjunct1, symmetric],
    assumption+)

lemma prime_factors_characterization'_nat: 
  "finite {p. 0 < f (p::nat)} \<Longrightarrow>
    (ALL p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow>
      prime_factors (PROD p | 0 < f p . p ^ f p) = {p. 0 < f p}"
  apply (rule prime_factors_characterization_nat)
  apply auto
done

(* A minor glitch:*)

thm prime_factors_characterization'_nat 
    [where f = "%x. f (int (x::nat))", 
      transferred direction: nat "op <= (0::int)", rule_format]

(*
  Transfer isn't smart enough to know that the "0 < f p" should 
  remain a comparison between nats. But the transfer still works. 
*)

lemma primes_characterization'_int [rule_format]: 
    "finite {p. p >= 0 & 0 < f (p::int)} \<Longrightarrow>
      (ALL p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow>
        prime_factors (PROD p | p >=0 & 0 < f p . p ^ f p) = 
          {p. p >= 0 & 0 < f p}"

  apply (insert prime_factors_characterization'_nat 
    [where f = "%x. f (int (x::nat))", 
    transferred direction: nat "op <= (0::int)"])
  apply auto
done

lemma prime_factors_characterization_int: "S = {p. 0 < f (p::int)} \<Longrightarrow> 
    finite S \<Longrightarrow> (ALL p:S. prime p) \<Longrightarrow> n = (PROD p:S. p ^ f p) \<Longrightarrow>
      prime_factors n = S"
  apply simp
  apply (subgoal_tac "{p. 0 < f p} = {p. 0 <= p & 0 < f p}")
  apply (simp only:)
  apply (subst primes_characterization'_int)
  apply auto
  apply (auto simp add: prime_ge_0_int)
done

lemma multiplicity_characterization_nat: "S = {p. 0 < f (p::nat)} \<Longrightarrow> 
    finite S \<Longrightarrow> (ALL p:S. prime p) \<Longrightarrow> n = (PROD p:S. p ^ f p) \<Longrightarrow>
      multiplicity p n = f p"
  by (frule prime_factorization_unique_nat [THEN conjunct2, rule_format, 
    symmetric], auto)

lemma multiplicity_characterization'_nat: "finite {p. 0 < f (p::nat)} \<longrightarrow>
    (ALL p. 0 < f p \<longrightarrow> prime p) \<longrightarrow>
      multiplicity p (PROD p | 0 < f p . p ^ f p) = f p"
  apply (rule impI)+
  apply (rule multiplicity_characterization_nat)
  apply auto
done

lemma multiplicity_characterization'_int [rule_format]: 
  "finite {p. p >= 0 & 0 < f (p::int)} \<Longrightarrow>
    (ALL p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow> p >= 0 \<Longrightarrow>
      multiplicity p (PROD p | p >= 0 & 0 < f p . p ^ f p) = f p"

  apply (insert multiplicity_characterization'_nat 
    [where f = "%x. f (int (x::nat))", 
      transferred direction: nat "op <= (0::int)", rule_format])
  apply auto
done

lemma multiplicity_characterization_int: "S = {p. 0 < f (p::int)} \<Longrightarrow> 
    finite S \<Longrightarrow> (ALL p:S. prime p) \<Longrightarrow> n = (PROD p:S. p ^ f p) \<Longrightarrow>
      p >= 0 \<Longrightarrow> multiplicity p n = f p"
  apply simp
  apply (subgoal_tac "{p. 0 < f p} = {p. 0 <= p & 0 < f p}")
  apply (simp only:)
  apply (subst multiplicity_characterization'_int)
  apply auto
  apply (auto simp add: prime_ge_0_int)
done

lemma multiplicity_zero_nat [simp]: "multiplicity (p::nat) 0 = 0"
  by (simp add: multiplicity_nat_def multiset_prime_factorization_def)

lemma multiplicity_zero_int [simp]: "multiplicity (p::int) 0 = 0"
  by (simp add: multiplicity_int_def) 

lemma multiplicity_one_nat [simp]: "multiplicity p (1::nat) = 0"
  by (subst multiplicity_characterization_nat [where f = "%x. 0"], auto)

lemma multiplicity_one_int [simp]: "multiplicity p (1::int) = 0"
  by (simp add: multiplicity_int_def)

lemma multiplicity_prime_nat [simp]: "prime (p::nat) \<Longrightarrow> multiplicity p p = 1"
  apply (subst multiplicity_characterization_nat
      [where f = "(%q. if q = p then 1 else 0)"])
  apply auto
  apply (case_tac "x = p")
  apply auto
done

lemma multiplicity_prime_int [simp]: "prime (p::int) \<Longrightarrow> multiplicity p p = 1"
  unfolding prime_int_def multiplicity_int_def by auto

lemma multiplicity_prime_power_nat [simp]: "prime (p::nat) \<Longrightarrow> 
    multiplicity p (p^n) = n"
  apply (case_tac "n = 0")
  apply auto
  apply (subst multiplicity_characterization_nat
      [where f = "(%q. if q = p then n else 0)"])
  apply auto
  apply (case_tac "x = p")
  apply auto
done

lemma multiplicity_prime_power_int [simp]: "prime (p::int) \<Longrightarrow> 
    multiplicity p (p^n) = n"
  apply (frule prime_ge_0_int)
  apply (auto simp add: prime_int_def multiplicity_int_def nat_power_eq)
done

lemma multiplicity_nonprime_nat [simp]: "~ prime (p::nat) \<Longrightarrow> 
    multiplicity p n = 0"
  apply (case_tac "n = 0")
  apply auto
  apply (frule multiset_prime_factorization)
  apply (auto simp add: set_of_def multiplicity_nat_def)
done

lemma multiplicity_nonprime_int [simp]: "~ prime (p::int) \<Longrightarrow> multiplicity p n = 0"
  by (unfold multiplicity_int_def prime_int_def, auto)

lemma multiplicity_not_factor_nat [simp]: 
    "p ~: prime_factors (n::nat) \<Longrightarrow> multiplicity p n = 0"
  by (subst (asm) prime_factors_altdef_nat, auto)

lemma multiplicity_not_factor_int [simp]: 
    "p >= 0 \<Longrightarrow> p ~: prime_factors (n::int) \<Longrightarrow> multiplicity p n = 0"
  by (subst (asm) prime_factors_altdef_int, auto)

lemma multiplicity_product_aux_nat: "(k::nat) > 0 \<Longrightarrow> l > 0 \<Longrightarrow>
    (prime_factors k) Un (prime_factors l) = prime_factors (k * l) &
    (ALL p. multiplicity p k + multiplicity p l = multiplicity p (k * l))"
  apply (rule prime_factorization_unique_nat)
  apply (simp only: prime_factors_altdef_nat)
  apply auto
  apply (subst power_add)
  apply (subst setprod_timesf)
  apply (rule arg_cong2)back back
  apply (subgoal_tac "prime_factors k Un prime_factors l = prime_factors k Un 
      (prime_factors l - prime_factors k)")
  apply (erule ssubst)
  apply (subst setprod_Un_disjoint)
  apply auto
  apply (subgoal_tac "(\<Prod>p\<in>prime_factors l - prime_factors k. p ^ multiplicity p k) = 
      (\<Prod>p\<in>prime_factors l - prime_factors k. 1)")
  apply (erule ssubst)
  apply (simp add: setprod_1)
  apply (erule prime_factorization_nat)
  apply (rule setprod_cong, auto)
  apply (subgoal_tac "prime_factors k Un prime_factors l = prime_factors l Un 
      (prime_factors k - prime_factors l)")
  apply (erule ssubst)
  apply (subst setprod_Un_disjoint)
  apply auto
  apply (subgoal_tac "(\<Prod>p\<in>prime_factors k - prime_factors l. p ^ multiplicity p l) = 
      (\<Prod>p\<in>prime_factors k - prime_factors l. 1)")
  apply (erule ssubst)
  apply (simp add: setprod_1)
  apply (erule prime_factorization_nat)
  apply (rule setprod_cong, auto)
done

(* transfer doesn't have the same problem here with the right 
   choice of rules. *)

lemma multiplicity_product_aux_int: 
  assumes "(k::int) > 0" and "l > 0"
  shows 
    "(prime_factors k) Un (prime_factors l) = prime_factors (k * l) &
    (ALL p >= 0. multiplicity p k + multiplicity p l = multiplicity p (k * l))"

  apply (rule multiplicity_product_aux_nat [transferred, of l k])
  using prems apply auto
done

lemma prime_factors_product_nat: "(k::nat) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> prime_factors (k * l) = 
    prime_factors k Un prime_factors l"
  by (rule multiplicity_product_aux_nat [THEN conjunct1, symmetric])

lemma prime_factors_product_int: "(k::int) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> prime_factors (k * l) = 
    prime_factors k Un prime_factors l"
  by (rule multiplicity_product_aux_int [THEN conjunct1, symmetric])

lemma multiplicity_product_nat: "(k::nat) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> multiplicity p (k * l) = 
    multiplicity p k + multiplicity p l"
  by (rule multiplicity_product_aux_nat [THEN conjunct2, rule_format, 
      symmetric])

lemma multiplicity_product_int: "(k::int) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> p >= 0 \<Longrightarrow> 
    multiplicity p (k * l) = multiplicity p k + multiplicity p l"
  by (rule multiplicity_product_aux_int [THEN conjunct2, rule_format, 
      symmetric])

lemma multiplicity_setprod_nat: "finite S \<Longrightarrow> (ALL x : S. f x > 0) \<Longrightarrow> 
    multiplicity (p::nat) (PROD x : S. f x) = 
      (SUM x : S. multiplicity p (f x))"
  apply (induct set: finite)
  apply auto
  apply (subst multiplicity_product_nat)
  apply auto
done

(* Transfer is delicate here for two reasons: first, because there is
   an implicit quantifier over functions (f), and, second, because the 
   product over the multiplicity should not be translated to an integer 
   product.

   The way to handle the first is to use quantifier rules for functions.
   The way to handle the second is to turn off the offending rule.
*)

lemma transfer_nat_int_sum_prod_closure3:
  "(SUM x : A. int (f x)) >= 0"
  "(PROD x : A. int (f x)) >= 0"
  apply (rule setsum_nonneg, auto)
  apply (rule setprod_nonneg, auto)
done

declare TransferMorphism_nat_int[transfer 
  add return: transfer_nat_int_sum_prod_closure3
  del: transfer_nat_int_sum_prod2 (1)]

lemma multiplicity_setprod_int: "p >= 0 \<Longrightarrow> finite S \<Longrightarrow> 
  (ALL x : S. f x > 0) \<Longrightarrow> 
    multiplicity (p::int) (PROD x : S. f x) = 
      (SUM x : S. multiplicity p (f x))"

  apply (frule multiplicity_setprod_nat
    [where f = "%x. nat(int(nat(f x)))", 
      transferred direction: nat "op <= (0::int)"])
  apply auto
  apply (subst (asm) setprod_cong)
  apply (rule refl)
  apply (rule if_P)
  apply auto
  apply (rule setsum_cong)
  apply auto
done

declare TransferMorphism_nat_int[transfer 
  add return: transfer_nat_int_sum_prod2 (1)]

lemma multiplicity_prod_prime_powers_nat:
    "finite S \<Longrightarrow> (ALL p : S. prime (p::nat)) \<Longrightarrow>
       multiplicity p (PROD p : S. p ^ f p) = (if p : S then f p else 0)"
  apply (subgoal_tac "(PROD p : S. p ^ f p) = 
      (PROD p : S. p ^ (%x. if x : S then f x else 0) p)")
  apply (erule ssubst)
  apply (subst multiplicity_characterization_nat)
  prefer 5 apply (rule refl)
  apply (rule refl)
  apply auto
  apply (subst setprod_mono_one_right)
  apply assumption
  prefer 3
  apply (rule setprod_cong)
  apply (rule refl)
  apply auto
done

(* Here the issue with transfer is the implicit quantifier over S *)

lemma multiplicity_prod_prime_powers_int:
    "(p::int) >= 0 \<Longrightarrow> finite S \<Longrightarrow> (ALL p : S. prime p) \<Longrightarrow>
       multiplicity p (PROD p : S. p ^ f p) = (if p : S then f p else 0)"

  apply (subgoal_tac "int ` nat ` S = S")
  apply (frule multiplicity_prod_prime_powers_nat [where f = "%x. f(int x)" 
    and S = "nat ` S", transferred])
  apply auto
  apply (subst prime_int_def [symmetric])
  apply auto
  apply (subgoal_tac "xb >= 0")
  apply force
  apply (rule prime_ge_0_int)
  apply force
  apply (subst transfer_nat_int_set_return_embed)
  apply (unfold nat_set_def, auto)
done

lemma multiplicity_distinct_prime_power_nat: "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow>
    p ~= q \<Longrightarrow> multiplicity p (q^n) = 0"
  apply (subgoal_tac "q^n = setprod (%x. x^n) {q}")
  apply (erule ssubst)
  apply (subst multiplicity_prod_prime_powers_nat)
  apply auto
done

lemma multiplicity_distinct_prime_power_int: "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow>
    p ~= q \<Longrightarrow> multiplicity p (q^n) = 0"
  apply (frule prime_ge_0_int [of q])
  apply (frule multiplicity_distinct_prime_power_nat [transferred leaving: n]) 
  prefer 4
  apply assumption
  apply auto
done

lemma dvd_multiplicity_nat: 
    "(0::nat) < y \<Longrightarrow> x dvd y \<Longrightarrow> multiplicity p x <= multiplicity p y"
  apply (case_tac "x = 0")
  apply (auto simp add: dvd_def multiplicity_product_nat)
done

lemma dvd_multiplicity_int: 
    "(0::int) < y \<Longrightarrow> 0 <= x \<Longrightarrow> x dvd y \<Longrightarrow> p >= 0 \<Longrightarrow> 
      multiplicity p x <= multiplicity p y"
  apply (case_tac "x = 0")
  apply (auto simp add: dvd_def)
  apply (subgoal_tac "0 < k")
  apply (auto simp add: multiplicity_product_int)
  apply (erule zero_less_mult_pos)
  apply arith
done

lemma dvd_prime_factors_nat [intro]:
    "0 < (y::nat) \<Longrightarrow> x dvd y \<Longrightarrow> prime_factors x <= prime_factors y"
  apply (simp only: prime_factors_altdef_nat)
  apply auto
  apply (frule dvd_multiplicity_nat)
  apply auto
(* It is a shame that auto and arith don't get this. *)
  apply (erule order_less_le_trans)back
  apply assumption
done

lemma dvd_prime_factors_int [intro]:
    "0 < (y::int) \<Longrightarrow> 0 <= x \<Longrightarrow> x dvd y \<Longrightarrow> prime_factors x <= prime_factors y"
  apply (auto simp add: prime_factors_altdef_int)
  apply (erule order_less_le_trans)
  apply (rule dvd_multiplicity_int)
  apply auto
done

lemma multiplicity_dvd_nat: "0 < (x::nat) \<Longrightarrow> 0 < y \<Longrightarrow> 
    ALL p. multiplicity p x <= multiplicity p y \<Longrightarrow>
      x dvd y"
  apply (subst prime_factorization_nat [of x], assumption)
  apply (subst prime_factorization_nat [of y], assumption)
  apply (rule setprod_dvd_setprod_subset2)
  apply force
  apply (subst prime_factors_altdef_nat)+
  apply auto
(* Again, a shame that auto and arith don't get this. *)
  apply (drule_tac x = xa in spec, auto)
  apply (rule le_imp_power_dvd)
  apply blast
done

lemma multiplicity_dvd_int: "0 < (x::int) \<Longrightarrow> 0 < y \<Longrightarrow> 
    ALL p >= 0. multiplicity p x <= multiplicity p y \<Longrightarrow>
      x dvd y"
  apply (subst prime_factorization_int [of x], assumption)
  apply (subst prime_factorization_int [of y], assumption)
  apply (rule setprod_dvd_setprod_subset2)
  apply force
  apply (subst prime_factors_altdef_int)+
  apply auto
  apply (rule dvd_power_le)
  apply auto
  apply (drule_tac x = xa in spec)
  apply (erule impE)
  apply auto
done

lemma multiplicity_dvd'_nat: "(0::nat) < x \<Longrightarrow> 
    \<forall>p. prime p \<longrightarrow> multiplicity p x \<le> multiplicity p y \<Longrightarrow> x dvd y"
  apply (cases "y = 0")
  apply auto
  apply (rule multiplicity_dvd_nat, auto)
  apply (case_tac "prime p")
  apply auto
done

lemma multiplicity_dvd'_int: "(0::int) < x \<Longrightarrow> 0 <= y \<Longrightarrow>
    \<forall>p. prime p \<longrightarrow> multiplicity p x \<le> multiplicity p y \<Longrightarrow> x dvd y"
  apply (cases "y = 0")
  apply auto
  apply (rule multiplicity_dvd_int, auto)
  apply (case_tac "prime p")
  apply auto
done

lemma dvd_multiplicity_eq_nat: "0 < (x::nat) \<Longrightarrow> 0 < y \<Longrightarrow>
    (x dvd y) = (ALL p. multiplicity p x <= multiplicity p y)"
  by (auto intro: dvd_multiplicity_nat multiplicity_dvd_nat)

lemma dvd_multiplicity_eq_int: "0 < (x::int) \<Longrightarrow> 0 < y \<Longrightarrow>
    (x dvd y) = (ALL p >= 0. multiplicity p x <= multiplicity p y)"
  by (auto intro: dvd_multiplicity_int multiplicity_dvd_int)

lemma prime_factors_altdef2_nat: "(n::nat) > 0 \<Longrightarrow> 
    (p : prime_factors n) = (prime p & p dvd n)"
  apply (case_tac "prime p")
  apply auto
  apply (subst prime_factorization_nat [where n = n], assumption)
  apply (rule dvd_trans) 
  apply (rule dvd_power [where x = p and n = "multiplicity p n"])
  apply (subst (asm) prime_factors_altdef_nat, force)
  apply (rule dvd_setprod)
  apply auto  
  apply (subst prime_factors_altdef_nat)
  apply (subst (asm) dvd_multiplicity_eq_nat)
  apply auto
  apply (drule spec [where x = p])
  apply auto
done

lemma prime_factors_altdef2_int: 
  assumes "(n::int) > 0" 
  shows "(p : prime_factors n) = (prime p & p dvd n)"

  apply (case_tac "p >= 0")
  apply (rule prime_factors_altdef2_nat [transferred])
  using prems apply auto
  apply (auto simp add: prime_ge_0_int prime_factors_ge_0_int)
done

lemma multiplicity_eq_nat:
  fixes x and y::nat 
  assumes [arith]: "x > 0" "y > 0" and
    mult_eq [simp]: "!!p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"

  apply (rule dvd_anti_sym)
  apply (auto intro: multiplicity_dvd'_nat) 
done

lemma multiplicity_eq_int:
  fixes x and y::int 
  assumes [arith]: "x > 0" "y > 0" and
    mult_eq [simp]: "!!p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"

  apply (rule dvd_anti_sym [transferred])
  apply (auto intro: multiplicity_dvd'_int) 
done


subsection {* An application *}

lemma gcd_eq_nat: 
  assumes pos [arith]: "x > 0" "y > 0"
  shows "gcd (x::nat) y = 
    (PROD p: prime_factors x Un prime_factors y. 
      p ^ (min (multiplicity p x) (multiplicity p y)))"
proof -
  def z == "(PROD p: prime_factors (x::nat) Un prime_factors y. 
      p ^ (min (multiplicity p x) (multiplicity p y)))"
  have [arith]: "z > 0"
    unfolding z_def by (rule setprod_pos_nat, auto)
  have aux: "!!p. prime p \<Longrightarrow> multiplicity p z = 
      min (multiplicity p x) (multiplicity p y)"
    unfolding z_def
    apply (subst multiplicity_prod_prime_powers_nat)
    apply (auto simp add: multiplicity_not_factor_nat)
    done
  have "z dvd x" 
    by (intro multiplicity_dvd'_nat, auto simp add: aux)
  moreover have "z dvd y" 
    by (intro multiplicity_dvd'_nat, auto simp add: aux)
  moreover have "ALL w. w dvd x & w dvd y \<longrightarrow> w dvd z"
    apply auto
    apply (case_tac "w = 0", auto)
    apply (erule multiplicity_dvd'_nat)
    apply (auto intro: dvd_multiplicity_nat simp add: aux)
    done
  ultimately have "z = gcd x y"
    by (subst gcd_unique_nat [symmetric], blast)
  thus ?thesis
    unfolding z_def by auto
qed

lemma lcm_eq_nat: 
  assumes pos [arith]: "x > 0" "y > 0"
  shows "lcm (x::nat) y = 
    (PROD p: prime_factors x Un prime_factors y. 
      p ^ (max (multiplicity p x) (multiplicity p y)))"
proof -
  def z == "(PROD p: prime_factors (x::nat) Un prime_factors y. 
      p ^ (max (multiplicity p x) (multiplicity p y)))"
  have [arith]: "z > 0"
    unfolding z_def by (rule setprod_pos_nat, auto)
  have aux: "!!p. prime p \<Longrightarrow> multiplicity p z = 
      max (multiplicity p x) (multiplicity p y)"
    unfolding z_def
    apply (subst multiplicity_prod_prime_powers_nat)
    apply (auto simp add: multiplicity_not_factor_nat)
    done
  have "x dvd z" 
    by (intro multiplicity_dvd'_nat, auto simp add: aux)
  moreover have "y dvd z" 
    by (intro multiplicity_dvd'_nat, auto simp add: aux)
  moreover have "ALL w. x dvd w & y dvd w \<longrightarrow> z dvd w"
    apply auto
    apply (case_tac "w = 0", auto)
    apply (rule multiplicity_dvd'_nat)
    apply (auto intro: dvd_multiplicity_nat simp add: aux)
    done
  ultimately have "z = lcm x y"
    by (subst lcm_unique_nat [symmetric], blast)
  thus ?thesis
    unfolding z_def by auto
qed

lemma multiplicity_gcd_nat: 
  assumes [arith]: "x > 0" "y > 0"
  shows "multiplicity (p::nat) (gcd x y) = 
    min (multiplicity p x) (multiplicity p y)"

  apply (subst gcd_eq_nat)
  apply auto
  apply (subst multiplicity_prod_prime_powers_nat)
  apply auto
done

lemma multiplicity_lcm_nat: 
  assumes [arith]: "x > 0" "y > 0"
  shows "multiplicity (p::nat) (lcm x y) = 
    max (multiplicity p x) (multiplicity p y)"

  apply (subst lcm_eq_nat)
  apply auto
  apply (subst multiplicity_prod_prime_powers_nat)
  apply auto
done

lemma gcd_lcm_distrib_nat: "gcd (x::nat) (lcm y z) = lcm (gcd x y) (gcd x z)"
  apply (case_tac "x = 0 | y = 0 | z = 0") 
  apply auto
  apply (rule multiplicity_eq_nat)
  apply (auto simp add: multiplicity_gcd_nat multiplicity_lcm_nat 
      lcm_pos_nat)
done

lemma gcd_lcm_distrib_int: "gcd (x::int) (lcm y z) = lcm (gcd x y) (gcd x z)"
  apply (subst (1 2 3) gcd_abs_int)
  apply (subst lcm_abs_int)
  apply (subst (2) abs_of_nonneg)
  apply force
  apply (rule gcd_lcm_distrib_nat [transferred])
  apply auto
done

end
