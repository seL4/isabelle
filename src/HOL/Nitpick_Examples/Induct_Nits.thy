(*  Title:      HOL/Nitpick_Examples/Induct_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick applied to (co)inductive definitions.
*)

header {* Examples Featuring Nitpick Applied to (Co)inductive Definitions *}

theory Induct_Nits
imports Main
begin

nitpick_params [verbose, card = 1\<emdash>8, unary_ints,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

inductive p1 :: "nat \<Rightarrow> bool" where
"p1 0" |
"p1 n \<Longrightarrow> p1 (n + 2)"

coinductive q1 :: "nat \<Rightarrow> bool" where
"q1 0" |
"q1 n \<Longrightarrow> q1 (n + 2)"

lemma "p1 = q1"
nitpick [expect = none]
nitpick [wf, expect = none]
nitpick [non_wf, expect = none]
nitpick [non_wf, dont_star_linear_preds, expect = none]
oops

lemma "p1 \<noteq> q1"
nitpick [expect = potential]
nitpick [wf, expect = potential]
nitpick [non_wf, expect = potential]
nitpick [non_wf, dont_star_linear_preds, expect = potential]
oops

lemma "p1 (n - 2) \<Longrightarrow> p1 n"
nitpick [expect = genuine]
nitpick [non_wf, expect = genuine]
nitpick [non_wf, dont_star_linear_preds, expect = genuine]
oops

lemma "q1 (n - 2) \<Longrightarrow> q1 n"
nitpick [expect = genuine]
nitpick [non_wf, expect = genuine]
nitpick [non_wf, dont_star_linear_preds, expect = genuine]
oops

inductive p2 :: "nat \<Rightarrow> bool" where
"p2 n \<Longrightarrow> p2 n"

coinductive q2 :: "nat \<Rightarrow> bool" where
"q2 n \<Longrightarrow> q2 n"

lemma "p2 = {}"
nitpick [expect = none]
nitpick [dont_star_linear_preds, expect = none]
sorry

lemma "q2 = {}"
nitpick [expect = genuine]
nitpick [dont_star_linear_preds, expect = genuine]
nitpick [wf, expect = quasi_genuine]
oops

lemma "p2 = UNIV"
nitpick [expect = genuine]
nitpick [dont_star_linear_preds, expect = genuine]
oops

lemma "q2 = UNIV"
nitpick [expect = none]
nitpick [dont_star_linear_preds, expect = none]
nitpick [wf, expect = quasi_genuine]
sorry

lemma "p2 = q2"
nitpick [expect = genuine]
nitpick [dont_star_linear_preds, expect = genuine]
oops

lemma "p2 n"
nitpick [expect = genuine]
nitpick [dont_star_linear_preds, expect = genuine]
nitpick [dont_specialize, expect = genuine]
oops

lemma "q2 n"
nitpick [expect = none]
nitpick [dont_star_linear_preds, expect = none]
sorry

lemma "\<not> p2 n"
nitpick [expect = none]
nitpick [dont_star_linear_preds, expect = none]
sorry

lemma "\<not> q2 n"
nitpick [expect = genuine]
nitpick [dont_star_linear_preds, expect = genuine]
nitpick [dont_specialize, expect = genuine]
oops

inductive p3 and p4 where
"p3 0" |
"p3 n \<Longrightarrow> p4 (Suc n)" |
"p4 n \<Longrightarrow> p3 (Suc n)"

coinductive q3 and q4 where
"q3 0" |
"q3 n \<Longrightarrow> q4 (Suc n)" |
"q4 n \<Longrightarrow> q3 (Suc n)"

lemma "p3 = q3"
nitpick [expect = none]
nitpick [non_wf, expect = none]
sorry

lemma "p4 = q4"
nitpick [expect = none]
nitpick [non_wf, expect = none]
sorry

lemma "p3 = UNIV - p4"
nitpick [expect = none]
nitpick [non_wf, expect = none]
sorry

lemma "q3 = UNIV - q4"
nitpick [expect = none]
nitpick [non_wf, expect = none]
sorry

lemma "p3 \<inter> q4 \<noteq> {}"
nitpick [expect = potential]
nitpick [non_wf, expect = potential]
sorry

lemma "q3 \<inter> p4 \<noteq> {}"
nitpick [expect = potential]
nitpick [non_wf, expect = potential]
sorry

lemma "p3 \<union> q4 \<noteq> UNIV"
nitpick [expect = potential]
nitpick [non_wf, expect = potential]
sorry

lemma "q3 \<union> p4 \<noteq> UNIV"
nitpick [expect = potential]
nitpick [non_wf, expect = potential]
sorry

end
