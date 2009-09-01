(*  Author:     Thomas Marthedal Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Fundamental Theorem of Arithmetic (unique factorization into primes) *}

theory Factorization
imports Main "~~/src/HOL/Old_Number_Theory/Primes" Permutation
begin


subsection {* Definitions *}

definition
  primel :: "nat list => bool" where
  "primel xs = (\<forall>p \<in> set xs. prime p)"

consts
  nondec :: "nat list => bool "
  prod :: "nat list => nat"
  oinsert :: "nat => nat list => nat list"
  sort :: "nat list => nat list"

primrec
  "nondec [] = True"
  "nondec (x # xs) = (case xs of [] => True | y # ys => x \<le> y \<and> nondec xs)"

primrec
  "prod [] = Suc 0"
  "prod (x # xs) = x * prod xs"

primrec
  "oinsert x [] = [x]"
  "oinsert x (y # ys) = (if x \<le> y then x # y # ys else y # oinsert x ys)"

primrec
  "sort [] = []"
  "sort (x # xs) = oinsert x (sort xs)"


subsection {* Arithmetic *}

lemma one_less_m: "(m::nat) \<noteq> m * k ==> m \<noteq> Suc 0 ==> Suc 0 < m"
  apply (cases m)
   apply auto
  done

lemma one_less_k: "(m::nat) \<noteq> m * k ==> Suc 0 < m * k ==> Suc 0 < k"
  apply (cases k)
   apply auto
  done

lemma mult_left_cancel: "(0::nat) < k ==> k * n = k * m ==> n = m"
  apply auto
  done

lemma mn_eq_m_one: "(0::nat) < m ==> m * n = m ==> n = Suc 0"
  apply (cases n)
   apply auto
  done

lemma prod_mn_less_k:
    "(0::nat) < n ==> 0 < k ==> Suc 0 < m ==> m * n = k ==> n < k"
  apply (induct m)
   apply auto
  done


subsection {* Prime list and product *}

lemma prod_append: "prod (xs @ ys) = prod xs * prod ys"
  apply (induct xs)
   apply (simp_all add: mult_assoc)
  done

lemma prod_xy_prod:
    "prod (x # xs) = prod (y # ys) ==> x * prod xs = y * prod ys"
  apply auto
  done

lemma primel_append: "primel (xs @ ys) = (primel xs \<and> primel ys)"
  apply (unfold primel_def)
  apply auto
  done

lemma prime_primel: "prime n ==> primel [n] \<and> prod [n] = n"
  apply (unfold primel_def)
  apply auto
  done

lemma prime_nd_one: "prime p ==> \<not> p dvd Suc 0"
  apply (unfold prime_def dvd_def)
  apply auto
  done

lemma hd_dvd_prod: "prod (x # xs) = prod ys ==> x dvd (prod ys)" 
  by (metis dvd_mult_left dvd_refl prod.simps(2))

lemma primel_tl: "primel (x # xs) ==> primel xs"
  apply (unfold primel_def)
  apply auto
  done

lemma primel_hd_tl: "(primel (x # xs)) = (prime x \<and> primel xs)"
  apply (unfold primel_def)
  apply auto
  done

lemma primes_eq: "prime p ==> prime q ==> p dvd q ==> p = q"
  apply (unfold prime_def)
  apply auto
  done

lemma primel_one_empty: "primel xs ==> prod xs = Suc 0 ==> xs = []"
  apply (cases xs)
   apply (simp_all add: primel_def prime_def)
  done

lemma prime_g_one: "prime p ==> Suc 0 < p"
  apply (unfold prime_def)
  apply auto
  done

lemma prime_g_zero: "prime p ==> 0 < p"
  apply (unfold prime_def)
  apply auto
  done

lemma primel_nempty_g_one:
    "primel xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Suc 0 < prod xs"
  apply (induct xs)
   apply simp
  apply (fastsimp simp: primel_def prime_def elim: one_less_mult)
  done

lemma primel_prod_gz: "primel xs ==> 0 < prod xs"
  apply (induct xs)
   apply (auto simp: primel_def prime_def)
  done


subsection {* Sorting *}

lemma nondec_oinsert: "nondec xs \<Longrightarrow> nondec (oinsert x xs)"
  apply (induct xs)
   apply simp
   apply (case_tac xs)
    apply (simp_all cong del: list.weak_case_cong)
  done

lemma nondec_sort: "nondec (sort xs)"
  apply (induct xs)
   apply simp_all
  apply (erule nondec_oinsert)
  done

lemma x_less_y_oinsert: "x \<le> y ==> l = y # ys ==> x # l = oinsert x l"
  apply simp_all
  done

lemma nondec_sort_eq [rule_format]: "nondec xs \<longrightarrow> xs = sort xs"
  apply (induct xs)
   apply safe
    apply simp_all
   apply (case_tac xs)
    apply simp_all
  apply (case_tac xs)
   apply simp
  apply (rule_tac y = aa and ys = list in x_less_y_oinsert)
   apply simp_all
  done

lemma oinsert_x_y: "oinsert x (oinsert y l) = oinsert y (oinsert x l)"
  apply (induct l)
  apply auto
  done


subsection {* Permutation *}

lemma perm_primel [rule_format]: "xs <~~> ys ==> primel xs --> primel ys"
  apply (unfold primel_def)
  apply (induct set: perm)
     apply simp
    apply simp
   apply (simp (no_asm))
   apply blast
  apply blast
  done

lemma perm_prod: "xs <~~> ys ==> prod xs = prod ys"
  apply (induct set: perm)
     apply (simp_all add: mult_ac)
  done

lemma perm_subst_oinsert: "xs <~~> ys ==> oinsert a xs <~~> oinsert a ys"
  apply (induct set: perm)
     apply auto
  done

lemma perm_oinsert: "x # xs <~~> oinsert x xs"
  apply (induct xs)
   apply auto
  done

lemma perm_sort: "xs <~~> sort xs"
  apply (induct xs)
  apply (auto intro: perm_oinsert elim: perm_subst_oinsert)
  done

lemma perm_sort_eq: "xs <~~> ys ==> sort xs = sort ys"
  apply (induct set: perm)
     apply (simp_all add: oinsert_x_y)
  done


subsection {* Existence *}

lemma ex_nondec_lemma:
    "primel xs ==> \<exists>ys. primel ys \<and> nondec ys \<and> prod ys = prod xs"
  apply (blast intro: nondec_sort perm_prod perm_primel perm_sort perm_sym)
  done

lemma not_prime_ex_mk:
  "Suc 0 < n \<and> \<not> prime n ==>
    \<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k"
  apply (unfold prime_def dvd_def)
  apply (auto intro: n_less_m_mult_n n_less_n_mult_m one_less_m one_less_k)
  done

lemma split_primel:
  "primel xs \<Longrightarrow> primel ys \<Longrightarrow> \<exists>l. primel l \<and> prod l = prod xs * prod ys"
  apply (rule exI)
  apply safe
   apply (rule_tac [2] prod_append)
  apply (simp add: primel_append)
  done

lemma factor_exists [rule_format]: "Suc 0 < n --> (\<exists>l. primel l \<and> prod l = n)"
  apply (induct n rule: nat_less_induct)
  apply (rule impI)
  apply (case_tac "prime n")
   apply (rule exI)
   apply (erule prime_primel)
  apply (cut_tac n = n in not_prime_ex_mk)
   apply (auto intro!: split_primel)
  done

lemma nondec_factor_exists: "Suc 0 < n ==> \<exists>l. primel l \<and> nondec l \<and> prod l = n"
  apply (erule factor_exists [THEN exE])
  apply (blast intro!: ex_nondec_lemma)
  done


subsection {* Uniqueness *}

lemma prime_dvd_mult_list [rule_format]:
    "prime p ==> p dvd (prod xs) --> (\<exists>m. m:set xs \<and> p dvd m)"
  apply (induct xs)
   apply (force simp add: prime_def)
   apply (force dest: prime_dvd_mult)
  done

lemma hd_xs_dvd_prod:
  "primel (x # xs) ==> primel ys ==> prod (x # xs) = prod ys
    ==> \<exists>m. m \<in> set ys \<and> x dvd m"
  apply (rule prime_dvd_mult_list)
   apply (simp add: primel_hd_tl)
  apply (erule hd_dvd_prod)
  done

lemma prime_dvd_eq: "primel (x # xs) ==> primel ys ==> m \<in> set ys ==> x dvd m ==> x = m"
  apply (rule primes_eq)
    apply (auto simp add: primel_def primel_hd_tl)
  done

lemma hd_xs_eq_prod:
  "primel (x # xs) ==>
    primel ys ==> prod (x # xs) = prod ys ==> x \<in> set ys"
  apply (frule hd_xs_dvd_prod)
    apply auto
  apply (drule prime_dvd_eq)
     apply auto
  done

lemma perm_primel_ex:
  "primel (x # xs) ==>
    primel ys ==> prod (x # xs) = prod ys ==> \<exists>l. ys <~~> (x # l)"
  apply (rule exI)
  apply (rule perm_remove)
  apply (erule hd_xs_eq_prod)
   apply simp_all
  done

lemma primel_prod_less:
  "primel (x # xs) ==>
    primel ys ==> prod (x # xs) = prod ys ==> prod xs < prod ys"
  by (metis less_asym linorder_neqE_nat mult_less_cancel2 nat_0_less_mult_iff
    nat_less_le nat_mult_1 prime_def primel_hd_tl primel_prod_gz prod.simps(2))

lemma prod_one_empty:
    "primel xs ==> p * prod xs = p ==> prime p ==> xs = []"
  apply (auto intro: primel_one_empty simp add: prime_def)
  done

lemma uniq_ex_aux:
  "\<forall>m. m < prod ys --> (\<forall>xs ys. primel xs \<and> primel ys \<and>
      prod xs = prod ys \<and> prod xs = m --> xs <~~> ys) ==>
    primel list ==> primel x ==> prod list = prod x ==> prod x < prod ys
    ==> x <~~> list"
  apply simp
  done

lemma factor_unique [rule_format]:
  "\<forall>xs ys. primel xs \<and> primel ys \<and> prod xs = prod ys \<and> prod xs = n
    --> xs <~~> ys"
  apply (induct n rule: nat_less_induct)
  apply safe
  apply (case_tac xs)
   apply (force intro: primel_one_empty)
  apply (rule perm_primel_ex [THEN exE])
     apply simp_all
  apply (rule perm.trans [THEN perm_sym])
  apply assumption
  apply (rule perm.Cons)
  apply (case_tac "x = []")
   apply (metis perm_prod perm_refl prime_primel primel_hd_tl primel_tl prod_one_empty)
  apply (metis nat_0_less_mult_iff nat_mult_eq_cancel1 perm_primel perm_prod primel_prod_gz primel_prod_less primel_tl prod.simps(2))
  done

lemma perm_nondec_unique:
    "xs <~~> ys ==> nondec xs ==> nondec ys ==> xs = ys"
  by (metis nondec_sort_eq perm_sort_eq)

theorem unique_prime_factorization [rule_format]:
    "\<forall>n. Suc 0 < n --> (\<exists>!l. primel l \<and> nondec l \<and> prod l = n)"
  by (metis factor_unique nondec_factor_exists perm_nondec_unique)

end
