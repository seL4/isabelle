theory Reverse
imports Define_Time_Function
begin

time_fun append
time_fun rev

lemma T_append: "T_append xs ys = length xs + 1"
by(induction xs) auto

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

end