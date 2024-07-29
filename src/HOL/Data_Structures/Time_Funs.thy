(*
  File:    Data_Structures/Time_Functions.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Time functions for various standard library operations\<close>
theory Time_Funs
  imports Define_Time_Function
begin

time_fun "(@)"

lemma T_append: "T_append xs ys = length xs + 1"
by(induction xs) auto

text \<open>Automatic definition of \<open>T_length\<close> is cumbersome because of the type class for \<open>size\<close>.\<close>

fun T_length :: "'a list \<Rightarrow> nat" where
  "T_length [] = 1"
| "T_length (x # xs) = T_length xs + 1"

lemma T_length_eq: "T_length xs = length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_length.simps

time_fun map

lemma T_map_eq: "T_map T_f xs = (\<Sum>x\<leftarrow>xs. T_f x) + length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_map.simps


fun T_filter  :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_filter T_p [] = 1"
| "T_filter T_p (x # xs) = T_p x + T_filter T_p xs + 1"

lemma T_filter_eq: "T_filter T_p xs = (\<Sum>x\<leftarrow>xs. T_p x) + length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_filter.simps

time_fun nth

lemma T_nth_eq: "n < length xs \<Longrightarrow> T_nth xs n = n + 1"
  by (induction xs n rule: T_nth.induct) (auto split: nat.splits)

lemmas [simp del] = T_nth.simps

time_fun take
time_fun drop

lemma T_take_eq: "T_take n xs = min n (length xs) + 1"
  by (induction xs arbitrary: n) (auto split: nat.splits)

lemma T_drop_eq: "T_drop n xs = min n (length xs) + 1"
  by (induction xs arbitrary: n) (auto split: nat.splits)
  
end
