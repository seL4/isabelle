(*  Title:      HOL/Isar_Examples/Group_Notepad.thy
    Author:     Makarius
*)

section \<open>Some algebraic identities derived from group axioms -- proof notepad version\<close>

theory Group_Notepad
  imports Main
begin

notepad
begin
  txt \<open>hypothetical group axiomatization\<close>

  fix prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<odot>\<close> 70)
    and one :: "'a"
    and inverse :: "'a \<Rightarrow> 'a"
  assume assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
    and left_one: "one \<odot> x = x"
    and left_inverse: "inverse x \<odot> x = one"
    for x y z

  txt \<open>some consequences\<close>

  have right_inverse: "x \<odot> inverse x = one" for x
  proof -
    have "x \<odot> inverse x = one \<odot> (x \<odot> inverse x)"
      by (simp only: left_one)
    also have "\<dots> = one \<odot> x \<odot> inverse x"
      by (simp only: assoc)
    also have "\<dots> = inverse (inverse x) \<odot> inverse x \<odot> x \<odot> inverse x"
      by (simp only: left_inverse)
    also have "\<dots> = inverse (inverse x) \<odot> (inverse x \<odot> x) \<odot> inverse x"
      by (simp only: assoc)
    also have "\<dots> = inverse (inverse x) \<odot> one \<odot> inverse x"
      by (simp only: left_inverse)
    also have "\<dots> = inverse (inverse x) \<odot> (one \<odot> inverse x)"
      by (simp only: assoc)
    also have "\<dots> = inverse (inverse x) \<odot> inverse x"
      by (simp only: left_one)
    also have "\<dots> = one"
      by (simp only: left_inverse)
    finally show ?thesis .
  qed

  have right_one: "x \<odot> one = x" for x
  proof -
    have "x \<odot> one = x \<odot> (inverse x \<odot> x)"
      by (simp only: left_inverse)
    also have "\<dots> = x \<odot> inverse x \<odot> x"
      by (simp only: assoc)
    also have "\<dots> = one \<odot> x"
      by (simp only: right_inverse)
    also have "\<dots> = x"
      by (simp only: left_one)
    finally show ?thesis .
  qed

  have one_equality: "one = e" if eq: "e \<odot> x = x" for e x
  proof -
    have "one = x \<odot> inverse x"
      by (simp only: right_inverse)
    also have "\<dots> = (e \<odot> x) \<odot> inverse x"
      by (simp only: eq)
    also have "\<dots> = e \<odot> (x \<odot> inverse x)"
      by (simp only: assoc)
    also have "\<dots> = e \<odot> one"
      by (simp only: right_inverse)
    also have "\<dots> = e"
      by (simp only: right_one)
    finally show ?thesis .
  qed

  have inverse_equality: "inverse x = x'" if eq: "x' \<odot> x = one" for x x'
  proof -
    have "inverse x = one \<odot> inverse x"
      by (simp only: left_one)
    also have "\<dots> = (x' \<odot> x) \<odot> inverse x"
      by (simp only: eq)
    also have "\<dots> = x' \<odot> (x \<odot> inverse x)"
      by (simp only: assoc)
    also have "\<dots> = x' \<odot> one"
      by (simp only: right_inverse)
    also have "\<dots> = x'"
      by (simp only: right_one)
    finally show ?thesis .
  qed

end

end
