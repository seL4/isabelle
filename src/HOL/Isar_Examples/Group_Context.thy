(*  Title:      HOL/Isar_Examples/Group_Context.thy
    Author:     Makarius
*)

header {* Some algebraic identities derived from group axioms -- theory context version *}

theory Group_Context
imports Main
begin

text {* hypothetical group axiomatization *}

context
  fixes prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "**" 70)
    and one :: "'a"
    and inverse :: "'a => 'a"
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"
    and left_one: "one ** x = x"
    and left_inverse: "inverse x ** x = one"
begin

text {* some consequences *}

lemma right_inverse: "x ** inverse x = one"
proof -
  have "x ** inverse x = one ** (x ** inverse x)"
    by (simp only: left_one)
  also have "\<dots> = one ** x ** inverse x"
    by (simp only: assoc)
  also have "\<dots> = inverse (inverse x) ** inverse x ** x ** inverse x"
    by (simp only: left_inverse)
  also have "\<dots> = inverse (inverse x) ** (inverse x ** x) ** inverse x"
    by (simp only: assoc)
  also have "\<dots> = inverse (inverse x) ** one ** inverse x"
    by (simp only: left_inverse)
  also have "\<dots> = inverse (inverse x) ** (one ** inverse x)"
    by (simp only: assoc)
  also have "\<dots> = inverse (inverse x) ** inverse x"
    by (simp only: left_one)
  also have "\<dots> = one"
    by (simp only: left_inverse)
  finally show "x ** inverse x = one" .
qed

lemma right_one: "x ** one = x"
proof -
  have "x ** one = x ** (inverse x ** x)"
    by (simp only: left_inverse)
  also have "\<dots> = x ** inverse x ** x"
    by (simp only: assoc)
  also have "\<dots> = one ** x"
    by (simp only: right_inverse)
  also have "\<dots> = x"
    by (simp only: left_one)
  finally show "x ** one = x" .
qed

lemma one_equality:
  assumes eq: "e ** x = x"
  shows "one = e"
proof -
  have "one = x ** inverse x"
    by (simp only: right_inverse)
  also have "\<dots> = (e ** x) ** inverse x"
    by (simp only: eq)
  also have "\<dots> = e ** (x ** inverse x)"
    by (simp only: assoc)
  also have "\<dots> = e ** one"
    by (simp only: right_inverse)
  also have "\<dots> = e"
    by (simp only: right_one)
  finally show "one = e" .
qed

lemma inverse_equality:
  assumes eq: "x' ** x = one"
  shows "inverse x = x'"
proof -
  have "inverse x = one ** inverse x"
    by (simp only: left_one)
  also have "\<dots> = (x' ** x) ** inverse x"
    by (simp only: eq)
  also have "\<dots> = x' ** (x ** inverse x)"
    by (simp only: assoc)
  also have "\<dots> = x' ** one"
    by (simp only: right_inverse)
  also have "\<dots> = x'"
    by (simp only: right_one)
  finally show "inverse x = x'" .
qed

end

end
