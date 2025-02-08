(*
Author: Jonas Stahl

Nonstandard examples of the time function definition commands.
*)

theory Time_Examples
imports Define_Time_Function
begin

fun even :: "nat \<Rightarrow> bool"
  and odd :: "nat \<Rightarrow> bool" where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"
time_fun even odd

locale locTests =
  fixes f :: "'a \<Rightarrow> 'b"
   and  T_f :: "'a \<Rightarrow> nat"
begin

fun simple where
  "simple a = f a"
time_fun simple

fun even :: "'a list \<Rightarrow> 'b list" and odd :: "'a list \<Rightarrow> 'b list" where
  "even [] = []"
| "odd [] = []"
| "even (x#xs) = f x # odd xs"
| "odd (x#xs) = even xs"
time_fun even odd

fun locSum :: "nat list \<Rightarrow> nat" where
  "locSum [] = 0"
| "locSum (x#xs) = x + locSum xs"
time_fun locSum

fun map :: "'a list \<Rightarrow> 'b list" where
  "map [] = []"
| "map (x#xs) = f x # map xs"
time_fun map

end

definition "let_lambda a b c \<equiv> let lam = (\<lambda>a b. a + b) in lam a (lam b c)"
time_fun let_lambda

partial_function (tailrec) collatz :: "nat \<Rightarrow> bool" where
  "collatz n = (if n \<le> 1 then True
                else if n mod 2 = 0 then collatz (n div 2)
                else collatz (3 * n + 1))"

text \<open>This is the expected time function:\<close>
partial_function (option) T_collatz' :: "nat \<Rightarrow> nat option" where
  "T_collatz' n = (if n \<le> 1 then Some 0
                else if n mod 2 = 0 then Option.bind (T_collatz' (n div 2)) (\<lambda>k. Some (Suc k))
                else Option.bind (T_collatz' (3 * n + 1)) (\<lambda>k. Some (Suc k)))"
time_fun_0 "(mod)"
time_partial_function collatz

text \<open>Proof that they are the same up to 20:\<close>
lemma setIt: "P i \<Longrightarrow> \<forall>n \<in> {Suc i..j}. P n \<Longrightarrow> \<forall>n \<in> {i..j}. P n"
  by (metis atLeastAtMost_iff le_antisym not_less_eq_eq)
lemma "\<forall>n \<in> {2..20}. T_collatz n = T_collatz' n"
  apply (rule setIt, simp add: T_collatz.simps T_collatz'.simps, simp)+
  by (simp add: T_collatz.simps T_collatz'.simps)

end