(*  Title:       IntFloor.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001,2002  University of Edinburgh
Converted to Isar and polished by lcp
*)

header{*Floor and Ceiling Functions from the Reals to the Integers*}

theory IntFloor = Integration:

constdefs

  floor :: "real => int"
   "floor r == (LEAST n. r < real (n + (1::int)))"

  ceiling :: "real => int"
    "ceiling r == - floor (- r)"

syntax (xsymbols)
  floor :: "real => int"     ("\<lfloor>_\<rfloor>")
  ceiling :: "real => int"   ("\<lceil>_\<rceil>")



lemma number_of_less_real_of_int_iff [simp]:
     "((number_of n) < real (m::int)) = (number_of n < m)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma number_of_less_real_of_int_iff2 [simp]:
     "(real (m::int) < (number_of n)) = (m < number_of n)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma number_of_le_real_of_int_iff [simp]:
     "((number_of n) \<le> real (m::int)) = (number_of n \<le> m)"
by (simp add: linorder_not_less [symmetric])

lemma number_of_le_real_of_int_iff2 [simp]:
     "(real (m::int) \<le> (number_of n)) = (m \<le> number_of n)"
by (simp add: linorder_not_less [symmetric])

lemma floor_zero [simp]: "floor 0 = 0"
apply (simp add: floor_def)
apply (rule Least_equality, auto)
done

lemma floor_real_of_nat_zero [simp]: "floor (real (0::nat)) = 0"
by auto

lemma floor_real_of_nat [simp]: "floor (real (n::nat)) = int n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1])
apply (simp_all add: real_of_int_real_of_nat)
done

lemma floor_minus_real_of_nat [simp]: "floor (- real (n::nat)) = - int n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_minus [THEN subst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1])
apply (simp_all add: real_of_int_real_of_nat)
done

lemma floor_real_of_int [simp]: "floor (real (n::int)) = n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1], auto)
done

lemma floor_minus_real_of_int [simp]: "floor (- real (n::int)) = - n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_minus [THEN subst])
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1], auto)
done

lemma reals_Archimedean6:
     "0 \<le> r ==> \<exists>(n::nat). real (n - 1) \<le> r & r < real (n)"
apply (insert reals_Archimedean2 [of r], safe)
apply (frule_tac P = "%k. r < real k" and k = n and m = "%x. x"
       in ex_has_least_nat, auto)
apply (rule_tac x = x in exI)
apply (case_tac x, simp)
apply (rename_tac x')
apply (drule_tac x = x' in spec, simp)
done

lemma reals_Archimedean6a: "0 \<le> r ==> \<exists>n. real (n) \<le> r & r < real (Suc n)"
by (drule reals_Archimedean6, auto)

lemma reals_Archimedean_6b_int:
     "0 \<le> r ==> \<exists>n. real n \<le> r & r < real ((n::int) + 1)"
apply (drule reals_Archimedean6a, auto)
apply (rule_tac x = "int n" in exI)
apply (simp add: real_of_int_real_of_nat real_of_nat_Suc)
done

lemma reals_Archimedean_6c_int:
     "r < 0 ==> \<exists>n. real n \<le> r & r < real ((n::int) + 1)"
apply (rule reals_Archimedean_6b_int [of "-r", THEN exE], simp, auto)
apply (rename_tac n)
apply (drule real_le_imp_less_or_eq, auto)
apply (rule_tac x = "- n - 1" in exI)
apply (rule_tac [2] x = "- n" in exI, auto)
done

lemma real_lb_ub_int: " \<exists>(n::int). real n \<le> r & r < real ((n::int) + 1)"
apply (case_tac "r < 0")
apply (blast intro: reals_Archimedean_6c_int)
apply (simp only: linorder_not_less)
apply (blast intro: reals_Archimedean_6b_int reals_Archimedean_6c_int)
done

lemma lemma_floor:
  assumes a1: "real m \<le> r" and a2: "r < real n + 1"
  shows "m \<le> (n::int)"
proof -
  have "real m < real n + 1" by (rule order_le_less_trans)
  also have "... = real(n+1)" by simp
  finally have "m < n+1" by (simp only: real_of_int_less_iff)
  thus ?thesis by arith
qed

lemma real_of_int_floor_le [simp]: "real (floor r) \<le> r"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of r], safe)
apply (rule theI2, auto)
done

lemma floor_le: "x < y ==> floor x \<le> floor y"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of x])
apply (insert real_lb_ub_int [of y], safe)
apply (rule theI2)
apply (rule_tac [3] theI2, auto)
done

lemma floor_le2: "x \<le> y ==> floor x \<le> floor y"
by (auto dest: real_le_imp_less_or_eq simp add: floor_le)

lemma lemma_floor2: "real na < real (x::int) + 1 ==> na \<le> x"
by (auto intro: lemma_floor)

lemma real_of_int_floor_cancel [simp]:
    "(real (floor x) = x) = (\<exists>n::int. x = real n)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of x], erule exE)
apply (rule theI2)
apply (auto intro: lemma_floor)
done

lemma floor_eq: "[| real n < x; x < real n + 1 |] ==> floor x = n"
apply (simp add: floor_def)
apply (rule Least_equality)
apply (auto intro: lemma_floor)
done

lemma floor_eq2: "[| real n \<le> x; x < real n + 1 |] ==> floor x = n"
apply (simp add: floor_def)
apply (rule Least_equality)
apply (auto intro: lemma_floor)
done

lemma floor_eq3: "[| real n < x; x < real (Suc n) |] ==> nat(floor x) = n"
apply (rule inj_int [THEN injD])
apply (simp add: real_of_nat_Suc)
apply (simp add: real_of_nat_Suc floor_eq floor_eq [where n = "of_nat n"])
done

lemma floor_eq4: "[| real n \<le> x; x < real (Suc n) |] ==> nat(floor x) = n"
apply (drule order_le_imp_less_or_eq)
apply (auto intro: floor_eq3)
done

lemma floor_number_of_eq [simp]:
     "floor(number_of n :: real) = (number_of n :: int)"
apply (subst real_number_of [symmetric])
apply (rule floor_real_of_int)
done

lemma real_of_int_floor_ge_diff_one [simp]: "r - 1 \<le> real(floor r)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of r], safe)
apply (rule theI2)
apply (auto intro: lemma_floor)
done

lemma real_of_int_floor_add_one_ge [simp]: "r \<le> real(floor r) + 1"
apply (insert real_of_int_floor_ge_diff_one [of r])
apply (auto simp del: real_of_int_floor_ge_diff_one)
done


subsection{*Ceiling Function for Positive Reals*}

lemma ceiling_zero [simp]: "ceiling 0 = 0"
by (simp add: ceiling_def)

lemma ceiling_real_of_nat [simp]: "ceiling (real (n::nat)) = int n"
by (simp add: ceiling_def)

lemma ceiling_real_of_nat_zero [simp]: "ceiling (real (0::nat)) = 0"
by auto

lemma ceiling_floor [simp]: "ceiling (real (floor r)) = floor r"
by (simp add: ceiling_def)

lemma floor_ceiling [simp]: "floor (real (ceiling r)) = ceiling r"
by (simp add: ceiling_def)

lemma real_of_int_ceiling_ge [simp]: "r \<le> real (ceiling r)"
apply (simp add: ceiling_def)
apply (subst le_minus_iff, simp)
done

lemma ceiling_le: "x < y ==> ceiling x \<le> ceiling y"
by (simp add: floor_le ceiling_def)

lemma ceiling_le2: "x \<le> y ==> ceiling x \<le> ceiling y"
by (simp add: floor_le2 ceiling_def)

lemma real_of_int_ceiling_cancel [simp]:
     "(real (ceiling x) = x) = (\<exists>n::int. x = real n)"
apply (auto simp add: ceiling_def)
apply (drule arg_cong [where f = uminus], auto)
apply (rule_tac x = "-n" in exI, auto)
done

lemma ceiling_eq: "[| real n < x; x < real n + 1 |] ==> ceiling x = n + 1"
apply (simp add: ceiling_def)
apply (rule minus_equation_iff [THEN iffD1])
apply (simp add: floor_eq [where n = "-(n+1)"])
done

lemma ceiling_eq2: "[| real n < x; x \<le> real n + 1 |] ==> ceiling x = n + 1"
by (simp add: ceiling_def floor_eq2 [where n = "-(n+1)"])

lemma ceiling_eq3: "[| real n - 1 < x; x \<le> real n  |] ==> ceiling x = n"
by (simp add: ceiling_def floor_eq2 [where n = "-n"])

lemma ceiling_real_of_int [simp]: "ceiling (real (n::int)) = n"
by (simp add: ceiling_def)

lemma ceiling_number_of_eq [simp]:
     "ceiling (number_of n :: real) = (number_of n)"
apply (subst real_number_of [symmetric])
apply (rule ceiling_real_of_int)
done

lemma real_of_int_ceiling_diff_one_le [simp]: "real (ceiling r) - 1 \<le> r"
apply (rule neg_le_iff_le [THEN iffD1])
apply (simp add: ceiling_def diff_minus)
done

lemma real_of_int_ceiling_le_add_one [simp]: "real (ceiling r) \<le> r + 1"
apply (insert real_of_int_ceiling_diff_one_le [of r])
apply (simp del: real_of_int_ceiling_diff_one_le)
done

ML
{*
val number_of_less_real_of_int_iff = thm "number_of_less_real_of_int_iff";
val number_of_less_real_of_int_iff2 = thm "number_of_less_real_of_int_iff2";
val number_of_le_real_of_int_iff = thm "number_of_le_real_of_int_iff";
val number_of_le_real_of_int_iff2 = thm "number_of_le_real_of_int_iff2";
val floor_zero = thm "floor_zero";
val floor_real_of_nat_zero = thm "floor_real_of_nat_zero";
val floor_real_of_nat = thm "floor_real_of_nat";
val floor_minus_real_of_nat = thm "floor_minus_real_of_nat";
val floor_real_of_int = thm "floor_real_of_int";
val floor_minus_real_of_int = thm "floor_minus_real_of_int";
val reals_Archimedean6 = thm "reals_Archimedean6";
val reals_Archimedean6a = thm "reals_Archimedean6a";
val reals_Archimedean_6b_int = thm "reals_Archimedean_6b_int";
val reals_Archimedean_6c_int = thm "reals_Archimedean_6c_int";
val real_lb_ub_int = thm "real_lb_ub_int";
val lemma_floor = thm "lemma_floor";
val real_of_int_floor_le = thm "real_of_int_floor_le";
val floor_le = thm "floor_le";
val floor_le2 = thm "floor_le2";
val lemma_floor2 = thm "lemma_floor2";
val real_of_int_floor_cancel = thm "real_of_int_floor_cancel";
val floor_eq = thm "floor_eq";
val floor_eq2 = thm "floor_eq2";
val floor_eq3 = thm "floor_eq3";
val floor_eq4 = thm "floor_eq4";
val floor_number_of_eq = thm "floor_number_of_eq";
val real_of_int_floor_ge_diff_one = thm "real_of_int_floor_ge_diff_one";
val real_of_int_floor_add_one_ge = thm "real_of_int_floor_add_one_ge";
val ceiling_zero = thm "ceiling_zero";
val ceiling_real_of_nat = thm "ceiling_real_of_nat";
val ceiling_real_of_nat_zero = thm "ceiling_real_of_nat_zero";
val ceiling_floor = thm "ceiling_floor";
val floor_ceiling = thm "floor_ceiling";
val real_of_int_ceiling_ge = thm "real_of_int_ceiling_ge";
val ceiling_le = thm "ceiling_le";
val ceiling_le2 = thm "ceiling_le2";
val real_of_int_ceiling_cancel = thm "real_of_int_ceiling_cancel";
val ceiling_eq = thm "ceiling_eq";
val ceiling_eq2 = thm "ceiling_eq2";
val ceiling_eq3 = thm "ceiling_eq3";
val ceiling_real_of_int = thm "ceiling_real_of_int";
val ceiling_number_of_eq = thm "ceiling_number_of_eq";
val real_of_int_ceiling_diff_one_le = thm "real_of_int_ceiling_diff_one_le";
val real_of_int_ceiling_le_add_one = thm "real_of_int_ceiling_le_add_one";
*}


end
