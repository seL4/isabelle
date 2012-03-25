(*  Title:      HOL/ex/Code_Nat_examples.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Simple examples for Code\_Numeral\_Nat theory. *}

theory Code_Nat_examples
imports Complex_Main "~~/src/HOL/Library/Efficient_Nat"
begin

fun to_n :: "nat \<Rightarrow> nat list"
where
  "to_n 0 = []"
| "to_n (Suc 0) = []"
| "to_n (Suc (Suc 0)) = []"
| "to_n (Suc n) = n # to_n n"

definition naive_prime :: "nat \<Rightarrow> bool"
where
  "naive_prime n \<longleftrightarrow> n \<ge> 2 \<and> filter (\<lambda>m. n mod m = 0) (to_n n) = []"

primrec fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
| "fac (Suc n) = Suc n * fac n"

primrec harmonic :: "nat \<Rightarrow> rat"
where
  "harmonic 0 = 0"
| "harmonic (Suc n) = 1 / of_nat (Suc n) + harmonic n"

lemma "harmonic 200 \<ge> 5"
  by eval

lemma "(let (q, r) = quotient_of (harmonic 8) in q div r) \<ge> 2"
  by normalization

lemma "naive_prime 89"
  by eval

lemma "naive_prime 89"
  by normalization

lemma "\<not> naive_prime 87"
  by eval

lemma "\<not> naive_prime 87"
  by normalization

lemma "fac 10 > 3000000"
  by eval

lemma "fac 10 > 3000000"
  by normalization

end

