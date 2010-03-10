
header {* Various examples for transfer procedure *}

theory Transfer_Ex
imports Main
begin

lemma ex1: "(x::nat) + y = y + x"
  by auto

lemma "(0\<Colon>int) \<le> (y\<Colon>int) \<Longrightarrow> (0\<Colon>int) \<le> (x\<Colon>int) \<Longrightarrow> x + y = y + x"
  by (fact ex1 [transferred])

lemma ex2: "(a::nat) div b * b + a mod b = a"
  by (rule mod_div_equality)

lemma "(0\<Colon>int) \<le> (b\<Colon>int) \<Longrightarrow> (0\<Colon>int) \<le> (a\<Colon>int) \<Longrightarrow> a div b * b + a mod b = a"
  by (fact ex2 [transferred])

lemma ex3: "ALL (x::nat). ALL y. EX z. z >= x + y"
  by auto

lemma "\<forall>x\<ge>0\<Colon>int. \<forall>y\<ge>0\<Colon>int. \<exists>xa\<ge>0\<Colon>int. x + y \<le> xa"
  by (fact ex3 [transferred nat_int])

lemma ex4: "(x::nat) >= y \<Longrightarrow> (x - y) + y = x"
  by auto

lemma "(0\<Colon>int) \<le> (x\<Colon>int) \<Longrightarrow> (0\<Colon>int) \<le> (y\<Colon>int) \<Longrightarrow> y \<le> x \<Longrightarrow> tsub x y + y = x"
  by (fact ex4 [transferred])

lemma ex5: "(2::nat) * \<Sum>{..n} = n * (n + 1)"
  by (induct n rule: nat_induct, auto)

lemma "(0\<Colon>int) \<le> (n\<Colon>int) \<Longrightarrow> (2\<Colon>int) * \<Sum>{0\<Colon>int..n} = n * (n + (1\<Colon>int))"
  by (fact ex5 [transferred])

lemma "(0\<Colon>nat) \<le> (n\<Colon>nat) \<Longrightarrow> (2\<Colon>nat) * \<Sum>{0\<Colon>nat..n} = n * (n + (1\<Colon>nat))"
  by (fact ex5 [transferred, transferred])

theorem ex6: "0 <= (n::int) \<Longrightarrow> 2 * \<Sum>{0..n} = n * (n + 1)"
  by (rule ex5 [transferred])

lemma "(0\<Colon>nat) \<le> (n\<Colon>nat) \<Longrightarrow> (2\<Colon>nat) * \<Sum>{0\<Colon>nat..n} = n * (n + (1\<Colon>nat))"
  by (fact ex6 [transferred])

end