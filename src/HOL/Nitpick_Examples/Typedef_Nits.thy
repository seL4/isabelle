(*  Title:      HOL/Nitpick_Examples/Typedef_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick applied to typedefs.
*)

header {* Examples Featuring Nitpick Applied to Typedefs *}

theory Typedef_Nits
imports Complex_Main
begin

nitpick_params [verbose, card = 1\<emdash>4, sat_solver = MiniSat_JNI, max_threads = 1,
                timeout = 240]

definition "three = {0\<Colon>nat, 1, 2}"
typedef (open) three = three
unfolding three_def by blast

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma "x = (y\<Colon>three)"
nitpick [expect = genuine]
oops

definition "one_or_two = {undefined False\<Colon>'a, undefined True}"

typedef (open) 'a one_or_two = "one_or_two :: 'a set"
unfolding one_or_two_def by auto

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

definition "bounded = {n\<Colon>nat. finite (UNIV \<Colon> 'a set) \<longrightarrow> n < card (UNIV \<Colon> 'a set)}"

typedef (open) 'a bounded = "bounded(TYPE('a))"
unfolding bounded_def
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
nitpick [expect = potential] (* unfortunate *)
sorry

lemma "x \<noteq> (y\<Colon>(bool \<times> bool) bounded) \<Longrightarrow> z = x \<or> z = y"
nitpick [card = 1\<emdash>5, expect = genuine]
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
by (insert Rep_unit) simp

lemma "Rep_unit () = False"
nitpick [expect = genuine]
oops

lemma "Pair a b = Abs_prod (Pair_Rep a b)"
nitpick [card = 1\<emdash>2, expect = none]
by (rule Pair_def)

lemma "Pair a b = Abs_prod (Pair_Rep b a)"
nitpick [card = 1\<emdash>2, expect = none]
nitpick [dont_box, expect = genuine]
oops

lemma "fst (Abs_prod (Pair_Rep a b)) = a"
nitpick [card = 2, expect = none]
by (simp add: Pair_def [THEN sym])

lemma "fst (Abs_prod (Pair_Rep a b)) = b"
nitpick [card = 1\<emdash>2, expect = none]
nitpick [dont_box, expect = genuine]
oops

lemma "a \<noteq> a' \<Longrightarrow> Pair_Rep a b \<noteq> Pair_Rep a' b"
nitpick [expect = none]
apply (rule ccontr)
apply simp
apply (drule subst [where P = "\<lambda>r. Abs_prod r = Abs_prod (Pair_Rep a b)"])
 apply (rule refl)
by (simp add: Pair_def [THEN sym])

lemma "Abs_prod (Rep_prod a) = a"
nitpick [card = 2, expect = none]
by (rule Rep_prod_inverse)

lemma "Inl \<equiv> \<lambda>a. Abs_sum (Inl_Rep a)"
nitpick [card = 1, expect = none]
by (simp add: Inl_def o_def)

lemma "Inl \<equiv> \<lambda>a. Abs_sum (Inr_Rep a)"
nitpick [card = 1, card "'a + 'a" = 2, expect = genuine]
oops

lemma "Inl_Rep a \<noteq> Inr_Rep a"
nitpick [expect = none]
by (rule Inl_Rep_not_Inr_Rep)

lemma "Abs_sum (Rep_sum a) = a"
nitpick [card = 1, expect = none]
nitpick [card = 2, expect = none]
by (rule Rep_sum_inverse)

lemma "0::nat \<equiv> Abs_Nat Zero_Rep"
nitpick [expect = none]
by (rule Zero_nat_def_raw)

lemma "Suc n = Abs_Nat (Suc_Rep (Rep_Nat n))"
nitpick [expect = none]
by (rule Suc_def)

lemma "Suc n = Abs_Nat (Suc_Rep (Suc_Rep (Rep_Nat n)))"
nitpick [expect = genuine]
oops

lemma "Abs_Nat (Rep_Nat a) = a"
nitpick [expect = none]
by (rule Rep_Nat_inverse)

lemma "0 \<equiv> Abs_Integ (intrel `` {(0, 0)})"
(*nitpick [card = 1, unary_ints, max_potential = 0, expect = none] (?)*)
by (rule Zero_int_def_raw)

lemma "Abs_list (Rep_list a) = a"
nitpick [card = 1\<emdash>2, expect = none]
by (rule Rep_list_inverse)

record point =
  Xcoord :: int
  Ycoord :: int

lemma "Abs_point_ext (Rep_point_ext a) = a"
nitpick [expect = none]
by (fact Rep_point_ext_inverse)

lemma "Fract a b = of_int a / of_int b"
nitpick [card = 1, expect = none]
by (rule Fract_of_int_quotient)

lemma "Abs_Rat (Rep_Rat a) = a"
nitpick [card = 1, expect = none]
by (rule Rep_Rat_inverse)

end
