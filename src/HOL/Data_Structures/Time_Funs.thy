(*
  File:    Data_Structures/Time_Functions.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Time functions for various standard library operations\<close>
theory Time_Funs
  imports Main
begin

fun T_length :: "'a list \<Rightarrow> nat" where
  "T_length [] = 1"
| "T_length (x # xs) = T_length xs + 1"

lemma T_length_eq: "T_length xs = length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_length.simps


fun T_map  :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_map T_f [] = 1"
| "T_map T_f (x # xs) = T_f x + T_map T_f xs + 1"

lemma T_map_eq: "T_map T_f xs = (\<Sum>x\<leftarrow>xs. T_f x) + length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_map.simps


fun T_filter  :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_filter T_p [] = 1"
| "T_filter T_p (x # xs) = T_p x + T_filter T_p xs + 1"

lemma T_filter_eq: "T_filter T_p xs = (\<Sum>x\<leftarrow>xs. T_p x) + length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_filter.simps


fun T_nth :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "T_nth [] n = 1"
| "T_nth (x # xs) n = (case n of 0 \<Rightarrow> 1 | Suc n' \<Rightarrow> T_nth xs n' + 1)"

lemma T_nth_eq: "T_nth xs n = min n (length xs) + 1"
  by (induction xs n rule: T_nth.induct) (auto split: nat.splits)

lemmas [simp del] = T_nth.simps


fun T_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_take n [] = 1"
| "T_take n (x # xs) = (case n of 0 \<Rightarrow> 1 | Suc n' \<Rightarrow> T_take n' xs + 1)"

lemma T_take_eq: "T_take n xs = min n (length xs) + 1"
  by (induction xs arbitrary: n) (auto split: nat.splits)

fun T_drop :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_drop n [] = 1"
| "T_drop n (x # xs) = (case n of 0 \<Rightarrow> 1 | Suc n' \<Rightarrow> T_drop n' xs + 1)"

lemma T_drop_eq: "T_drop n xs = min n (length xs) + 1"
  by (induction xs arbitrary: n) (auto split: nat.splits)
  
  
end
