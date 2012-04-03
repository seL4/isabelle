(*  Title:      HOL/Isar_Examples/Group_Notepad.thy
    Author:     Makarius
*)

header {* Some algebraic identities derived from group axioms -- proof notepad version *}

theory Group_Notepad
imports Main
begin

notepad
begin
  txt {* hypothetical group axiomatization *}

  fix prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "**" 70)
    and one :: "'a"
    and inverse :: "'a => 'a"
  assume assoc: "\<And>x y z. (x ** y) ** z = x ** (y ** z)"
    and left_one: "\<And>x. one ** x = x"
    and left_inverse: "\<And>x. inverse x ** x = one"

  txt {* some consequences *}

  have right_inverse: "\<And>x. x ** inverse x = one"
  proof -
    fix x
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

  have right_one: "\<And>x. x ** one = x"
  proof -
    fix x
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

  have one_equality: "\<And>e x. e ** x = x \<Longrightarrow> one = e"
  proof -
    fix e x
    assume eq: "e ** x = x"
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

  have inverse_equality: "\<And>x x'. x' ** x = one \<Longrightarrow> inverse x = x'"
  proof -
    fix x x'
    assume eq: "x' ** x = one"
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
