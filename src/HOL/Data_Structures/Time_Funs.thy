(*
  File:    Data_Structures/Time_Functions.thy
  Author:  Manuel Eberl, TU München
*)

section \<open>Time functions for various standard library operations. Also defines \<open>itrev\<close>.\<close>

theory Time_Funs
  imports Define_Time_Function
begin

time_fun fst
time_fun snd

time_fun "(@)"

lemma T_append: "T_append xs ys = length xs + 1"
by(induction xs) auto

class T_size =
  fixes T_size :: "'a \<Rightarrow> nat"

instantiation list :: (_) T_size
begin

time_fun length

instance ..

end

abbreviation T_length :: "'a list \<Rightarrow> nat" where
"T_length \<equiv> T_size"

lemma T_length: "T_length xs = length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_size_list.simps

time_fun map

lemma T_map_simps [simp,code]:
  "T_map T_f [] = 1"
  "T_map T_f (x # xs) = T_f x + T_map T_f xs + 1"
by (simp_all add: T_map_def)

lemma T_map: "T_map T_f xs = (\<Sum>x\<leftarrow>xs. T_f x) + length xs + 1"
  by (induction xs) auto

lemmas [simp del] = T_map_simps

time_fun filter

lemma T_filter_simps [code]:
  "T_filter T_P [] = 1"
  "T_filter T_P (x # xs) = T_P x + T_filter T_P xs + 1"
by (simp_all add: T_filter_def)

lemma T_filter: "T_filter T_P xs = (\<Sum>x\<leftarrow>xs. T_P x) + length xs + 1"
by (induction xs) (auto simp: T_filter_simps)

time_fun nth

lemma T_nth: "n < length xs \<Longrightarrow> T_nth xs n = n + 1"
  by (induction xs n rule: T_nth.induct) (auto split: nat.splits)

lemmas [simp del] = T_nth.simps

time_fun take
time_fun drop

lemma T_take: "T_take n xs = min n (length xs) + 1"
  by (induction xs arbitrary: n) (auto split: nat.splits)

lemma T_drop: "T_drop n xs = min n (length xs) + 1"
  by (induction xs arbitrary: n) (auto split: nat.splits)

time_fun rev

lemma T_rev: "T_rev xs \<le> (length xs + 1)^2"
by(induction xs) (auto simp: T_append power2_eq_square)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x # ys)"

lemma itrev: "itrev xs ys = rev xs @ ys"
by(induction xs arbitrary: ys) auto

lemma itrev_Nil: "itrev xs [] = rev xs"
by(simp add: itrev)

time_fun itrev

lemma T_itrev: "T_itrev xs ys = length xs + 1"
by(induction xs arbitrary: ys) auto

time_fun tl

lemma T_tl: "T_tl xs = 0"
by (cases xs) simp_all

declare T_tl.simps[simp del]

end
