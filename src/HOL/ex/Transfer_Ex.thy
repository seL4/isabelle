
header {* Various examples for transfer procedure *}

theory Transfer_Ex
imports Complex_Main
begin

(* nat to int *)

lemma ex1: "(x::nat) + y = y + x"
  by auto

thm ex1 [transferred]

lemma ex2: "(a::nat) div b * b + a mod b = a"
  by (rule mod_div_equality)

thm ex2 [transferred]

lemma ex3: "ALL (x::nat). ALL y. EX z. z >= x + y"
  by auto

thm ex3 [transferred natint]

lemma ex4: "(x::nat) >= y \<Longrightarrow> (x - y) + y = x"
  by auto

thm ex4 [transferred]

lemma ex5: "(2::nat) * (SUM i <= n. i) = n * (n + 1)"
  by (induct n rule: nat_induct, auto)

thm ex5 [transferred]

theorem ex6: "0 <= (n::int) \<Longrightarrow> 2 * \<Sum>{0..n} = n * (n + 1)"
  by (rule ex5 [transferred])

thm ex6 [transferred]

thm ex5 [transferred, transferred]

end