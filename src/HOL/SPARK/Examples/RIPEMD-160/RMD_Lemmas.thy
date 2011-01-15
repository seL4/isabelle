(*  Title:      HOL/SPARK/Examples/RIPEMD-160/RMD_Lemmas.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory RMD_Lemmas
imports Main
begin

definition "fun_of_list i xs g j =
  (if j < i \<or> i + int (length xs) \<le> j then g j else xs ! nat (j - i))"

lemma fun_of_list_Nil [simp]: "fun_of_list i [] g = g"
  by (auto simp add: fun_eq_iff fun_of_list_def)

lemma fun_of_list_Cons [simp]:
  "fun_of_list i (x # xs) g = fun_of_list (i + 1) xs (g(i:=x))"
  by (auto simp add: fun_eq_iff fun_of_list_def nth_Cons'
    nat_diff_distrib [of "int (Suc 0)", simplified, symmetric]
    diff_diff_eq)

lemma nth_fun_of_list_eq:
  "0 \<le> i \<Longrightarrow> i < int (length xs) \<Longrightarrow> xs ! nat i = fun_of_list 0 xs g i"
  by (simp add: fun_of_list_def)

end
