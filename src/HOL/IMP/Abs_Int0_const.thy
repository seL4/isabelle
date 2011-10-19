(* Author: Tobias Nipkow *)

theory Abs_Int0_const
imports Abs_Int0
begin

subsection "Constant Propagation"

datatype cval = Const val | Any

fun rep_cval where
"rep_cval (Const n) = {n}" |
"rep_cval (Any) = UNIV"

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


interpretation Val_abs rep_cval Const plus_cval
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

interpretation Abs_Int rep_cval Const plus_cval
defines AI_const is AI
and aval'_const is aval'
and step_const is step
proof qed

text{* Straight line code: *}
definition "test1_const =
 ''y'' ::= N 7;
 ''z'' ::= Plus (V ''y'') (N 2);
 ''y'' ::= Plus (V ''x'') (N 0)"

text{* Conditional: *}
definition "test2_const =
 IF Less (N 41) (V ''x'') THEN ''x'' ::= N 5 ELSE ''x'' ::= N 5"

text{* Conditional, test is ignored: *}
definition "test3_const =
 ''x'' ::= N 42;
 IF Less (N 41) (V ''x'') THEN ''x'' ::= N 5 ELSE ''x'' ::= N 6"

text{* While: *}
definition "test4_const =
 ''x'' ::= N 0; WHILE Bc True DO ''x'' ::= N 0"

text{* While, test is ignored: *}
definition "test5_const =
 ''x'' ::= N 0; WHILE Less (V ''x'') (N 1) DO ''x'' ::= N 1"

text{* Iteration is needed: *}
definition "test6_const =
  ''x'' ::= N 0; ''y'' ::= N 0; ''z'' ::= N 2;
  WHILE Less (V ''x'') (N 1) DO (''x'' ::= V ''y''; ''y'' ::= V ''z'')"

text{* More iteration would be needed: *}
definition "test7_const =
  ''x'' ::= N 0; ''y'' ::= N 0; ''z'' ::= N 0; ''u'' ::= N 3;
  WHILE Less (V ''x'') (N 1)
  DO (''x'' ::= V ''y''; ''y'' ::= V ''z''; ''z'' ::= V ''u'')"

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
value [code] "show_acom_opt (AI_const test7_const)"

text{* Monotonicity: *}

interpretation Abs_Int_mono rep_cval Const plus_cval
proof
  case goal1 thus ?case
    by(auto simp: plus_cval_cases split: cval.split)
qed

end
