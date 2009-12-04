(*  Title:      HOL/Nitpick_Examples/Typedef_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Examples featuring Nitpick applied to typedefs.
*)

header {* Examples Featuring Nitpick Applied to Typedefs *}

theory Typedef_Nits
imports Main Rational
begin

nitpick_params [card = 1\<midarrow>4, timeout = 5 s]

typedef three = "{0\<Colon>nat, 1, 2}"
by blast

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma "x = (y\<Colon>three)"
nitpick [expect = genuine]
oops

typedef 'a one_or_two = "{undefined False\<Colon>'a, undefined True}"
by auto

lemma "x = (y\<Colon>unit one_or_two)"
nitpick [expect = none]
sorry

lemma "x = (y\<Colon>bool one_or_two)"
nitpick [expect = genuine]
oops

lemma "undefined False \<longleftrightarrow> undefined True \<Longrightarrow> x = (y\<Colon>bool one_or_two)"
nitpick [expect = none]
sorry

lemma "undefined False \<longleftrightarrow> undefined True \<Longrightarrow> \<exists>x (y\<Colon>bool one_or_two). x \<noteq> y"
nitpick [card = 1, expect = potential] (* unfortunate *)
oops

lemma "\<exists>x (y\<Colon>bool one_or_two). x \<noteq> y"
nitpick [card = 1, expect = potential] (* unfortunate *)
nitpick [card = 2, expect = none]
oops

typedef 'a bounded =
        "{n\<Colon>nat. finite (UNIV\<Colon>'a \<Rightarrow> bool) \<longrightarrow> n < card (UNIV\<Colon>'a \<Rightarrow> bool)}"
apply (rule_tac x = 0 in exI)
apply (case_tac "card UNIV = 0")
by auto

lemma "x = (y\<Colon>unit bounded)"
nitpick [expect = none]
sorry

lemma "x = (y\<Colon>bool bounded)"
nitpick [expect = genuine]
oops

lemma "x \<noteq> (y\<Colon>bool bounded) \<Longrightarrow> z = x \<or> z = y"
nitpick [expect = none]
sorry

lemma "x \<noteq> (y\<Colon>(bool \<times> bool) bounded) \<Longrightarrow> z = x \<or> z = y"
nitpick [card = 1\<midarrow>5, timeout = 10 s, expect = genuine]
oops

lemma "True \<equiv> ((\<lambda>x\<Colon>bool. x) = (\<lambda>x. x))"
nitpick [expect = none]
by (rule True_def)

lemma "False \<equiv> \<forall>P. P"
nitpick [expect = none]
by (rule False_def)

lemma "() = Abs_unit True"
nitpick [expect = none]
by (rule Unity_def)

lemma "() = Abs_unit False"
nitpick [expect = none]
by simp

lemma "Rep_unit () = True"
nitpick [expect = none]
by (insert Rep_unit) (simp add: unit_def)

lemma "Rep_unit () = False"
nitpick [expect = genuine]
oops

lemma "Pair a b \<equiv> Abs_Prod (Pair_Rep a b)"
nitpick [card = 1\<midarrow>2, expect = none]
by (rule Pair_def)

lemma "Pair a b \<equiv> Abs_Prod (Pair_Rep b a)"
nitpick [card = 1\<midarrow>2, expect = none]
nitpick [dont_box, expect = genuine]
oops

lemma "fst (Abs_Prod (Pair_Rep a b)) = a"
nitpick [card = 2, expect = none]
by (simp add: Pair_def [THEN symmetric])

lemma "fst (Abs_Prod (Pair_Rep a b)) = b"
nitpick [card = 1\<midarrow>2, expect = none]
nitpick [dont_box, expect = genuine]
oops

lemma "a \<noteq> a' \<Longrightarrow> Pair_Rep a b \<noteq> Pair_Rep a' b"
nitpick [expect = none]
apply (rule ccontr)
apply simp
apply (drule subst [where P = "\<lambda>r. Abs_Prod r = Abs_Prod (Pair_Rep a b)"])
 apply (rule refl)
by (simp add: Pair_def [THEN symmetric])

lemma "Abs_Prod (Rep_Prod a) = a"
nitpick [card = 2, expect = none]
by (rule Rep_Prod_inverse)

lemma "Inl \<equiv> \<lambda>a. Abs_Sum (Inl_Rep a)"
nitpick [card = 1, expect = none]
by (simp only: Inl_def o_def)

lemma "Inl \<equiv> \<lambda>a. Abs_Sum (Inr_Rep a)"
nitpick [card = 1, card "'a + 'a" = 2, expect = genuine]
oops

lemma "Inl_Rep a \<noteq> Inr_Rep a"
nitpick [expect = none]
by (rule Inl_Rep_not_Inr_Rep)

lemma "Abs_Sum (Rep_Sum a) = a"
nitpick [card = 1\<midarrow>2, timeout = 30 s, expect = none]
by (rule Rep_Sum_inverse)

lemma "0::nat \<equiv> Abs_Nat Zero_Rep"
(* nitpick [expect = none] FIXME *)
by (rule Zero_nat_def_raw)

lemma "Suc \<equiv> \<lambda>n. Abs_Nat (Suc_Rep (Rep_Nat n))"
(* nitpick [expect = none] FIXME *)
by (rule Suc_def)

lemma "Suc \<equiv> \<lambda>n. Abs_Nat (Suc_Rep (Suc_Rep (Rep_Nat n)))"
nitpick [expect = genuine]
oops

lemma "Abs_Nat (Rep_Nat a) = a"
nitpick [expect = none]
by (rule Rep_Nat_inverse)

lemma "0 \<equiv> Abs_Integ (intrel `` {(0, 0)})"
nitpick [card = 1, timeout = 30 s, max_potential = 0, expect = none]
by (rule Zero_int_def_raw)

lemma "Abs_Integ (Rep_Integ a) = a"
nitpick [card = 1, timeout = 30 s, max_potential = 0, expect = none]
by (rule Rep_Integ_inverse)

lemma "Abs_list (Rep_list a) = a"
nitpick [card = 1\<midarrow>2, timeout = 30 s, expect = none]
by (rule Rep_list_inverse)

record point =
  Xcoord :: int
  Ycoord :: int

lemma "Abs_point_ext_type (Rep_point_ext_type a) = a"
nitpick [expect = none]
by (rule Rep_point_ext_type_inverse)

lemma "Fract a b = of_int a / of_int b"
nitpick [card = 1, expect = none]
by (rule Fract_of_int_quotient)

lemma "Abs_Rat (Rep_Rat a) = a"
nitpick [card = 1, expect = none]
by (rule Rep_Rat_inverse)

end
