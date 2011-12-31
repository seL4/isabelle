(* Author: Tobias Nipkow *)

theory Abs_Int0_const
imports Abs_Int0 Abs_Int_Tests
begin

subsection "Constant Propagation"

datatype cval = Const val | Any

fun \<gamma>_cval where
"\<gamma>_cval (Const n) = {n}" |
"\<gamma>_cval (Any) = UNIV"

fun plus_cval where
"plus_cval (Const m) (Const n) = Const(m+n)" |
"plus_cval _ _ = Any"

lemma plus_cval_cases: "plus_cval a1 a2 =
  (case (a1,a2) of (Const m, Const n) \<Rightarrow> Const(m+n) | _ \<Rightarrow> Any)"
by(auto split: prod.split cval.split)

instantiation cval :: SL_top
begin

fun le_cval where
"_ \<sqsubseteq> Any = True" |
"Const n \<sqsubseteq> Const m = (n=m)" |
"Any \<sqsubseteq> Const _ = False"

fun join_cval where
"Const m \<squnion> Const n = (if n=m then Const m else Any)" |
"_ \<squnion> _ = Any"

definition "\<top> = Any"

instance
proof
  case goal1 thus ?case by (cases x) simp_all
next
  case goal2 thus ?case by(cases z, cases y, cases x, simp_all)
next
  case goal3 thus ?case by(cases x, cases y, simp_all)
next
  case goal4 thus ?case by(cases y, cases x, simp_all)
next
  case goal5 thus ?case by(cases z, cases y, cases x, simp_all)
next
  case goal6 thus ?case by(simp add: Top_cval_def)
qed

end


interpretation Val_abs
where \<gamma> = \<gamma>_cval and num' = Const and plus' = plus_cval
defines aval'_const is aval'
proof
  case goal1 thus ?case
    by(cases a, cases b, simp, simp, cases b, simp, simp)
next
  case goal2 show ?case by(simp add: Top_cval_def)
next
  case goal3 show ?case by simp
next
  case goal4 thus ?case
    by(auto simp: plus_cval_cases split: cval.split)
qed

interpretation Abs_Int
where \<gamma> = \<gamma>_cval and num' = Const and plus' = plus_cval
defines AI_const is AI
and step_const is step'
proof qed


text{* Monotonicity: *}

interpretation Abs_Int_mono
where \<gamma> = \<gamma>_cval and num' = Const and plus' = plus_cval
proof
  case goal1 thus ?case
    by(auto simp: plus_cval_cases split: cval.split)
qed


subsubsection "Tests"

value [code] "show_acom (((step_const \<top>)^^0) (\<bottom>\<^sub>c test1_const))"
value [code] "show_acom (((step_const \<top>)^^1) (\<bottom>\<^sub>c test1_const))"
value [code] "show_acom (((step_const \<top>)^^2) (\<bottom>\<^sub>c test1_const))"
value [code] "show_acom (((step_const \<top>)^^3) (\<bottom>\<^sub>c test1_const))"
value [code] "show_acom_opt (AI_const test1_const)"

value [code] "show_acom_opt (AI_const test2_const)"
value [code] "show_acom_opt (AI_const test3_const)"

value [code] "show_acom (((step_const \<top>)^^0) (\<bottom>\<^sub>c test4_const))"
value [code] "show_acom (((step_const \<top>)^^1) (\<bottom>\<^sub>c test4_const))"
value [code] "show_acom (((step_const \<top>)^^2) (\<bottom>\<^sub>c test4_const))"
value [code] "show_acom (((step_const \<top>)^^3) (\<bottom>\<^sub>c test4_const))"
value [code] "show_acom_opt (AI_const test4_const)"

value [code] "show_acom (((step_const \<top>)^^0) (\<bottom>\<^sub>c test5_const))"
value [code] "show_acom (((step_const \<top>)^^1) (\<bottom>\<^sub>c test5_const))"
value [code] "show_acom (((step_const \<top>)^^2) (\<bottom>\<^sub>c test5_const))"
value [code] "show_acom (((step_const \<top>)^^3) (\<bottom>\<^sub>c test5_const))"
value [code] "show_acom (((step_const \<top>)^^4) (\<bottom>\<^sub>c test5_const))"
value [code] "show_acom (((step_const \<top>)^^5) (\<bottom>\<^sub>c test5_const))"
value [code] "show_acom_opt (AI_const test5_const)"

value [code] "show_acom_opt (AI_const test6_const)"

end
