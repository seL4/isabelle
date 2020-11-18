theory Reverse
imports Main
begin

fun T_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
"T_append [] ys = 1" |
"T_append (x#xs) ys = T_append xs ys + 1"

fun T_rev :: "'a list \<Rightarrow> nat" where
"T_rev [] = 1" |
"T_rev (x#xs) = T_rev xs + T_append (rev xs) [x] + 1"

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

fun T_itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
"T_itrev [] ys = 1" |
"T_itrev (x#xs) ys = T_itrev xs (x # ys) + 1"

lemma T_itrev: "T_itrev xs ys = length xs + 1"
by(induction xs arbitrary: ys) auto

end