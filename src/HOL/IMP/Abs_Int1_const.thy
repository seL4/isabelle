(* Author: Tobias Nipkow *)

theory Abs_Int1_const
imports Abs_Int1
begin

subsection "Constant Propagation"

datatype const = Const val | Any

fun \<gamma>_const where
"\<gamma>_const (Const n) = {n}" |
"\<gamma>_const (Any) = UNIV"

fun plus_const where
"plus_const (Const m) (Const n) = Const(m+n)" |
"plus_const _ _ = Any"

lemma plus_const_cases: "plus_const a1 a2 =
  (case (a1,a2) of (Const m, Const n) \<Rightarrow> Const(m+n) | _ \<Rightarrow> Any)"
by(auto split: prod.split const.split)

instantiation const :: SL_top
begin

fun le_const where
"_ \<sqsubseteq> Any = True" |
"Const n \<sqsubseteq> Const m = (n=m)" |
"Any \<sqsubseteq> Const _ = False"

fun join_const where
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
  case goal6 thus ?case by(simp add: Top_const_def)
qed

end


interpretation Val_abs
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
proof
  case goal1 thus ?case
    by(cases a, cases b, simp, simp, cases b, simp, simp)
next
  case goal2 show ?case by(simp add: Top_const_def)
next
  case goal3 show ?case by simp
next
  case goal4 thus ?case
    by(auto simp: plus_const_cases split: const.split)
qed

interpretation Abs_Int
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
defines AI_const is AI and step_const is step' and aval'_const is aval'
..


subsubsection "Tests"

definition "steps c i = (step_const(top c) ^^ i) (bot c)"

value "show_acom (steps test1_const 0)"
value "show_acom (steps test1_const 1)"
value "show_acom (steps test1_const 2)"
value "show_acom (steps test1_const 3)"
value "show_acom_opt (AI_const test1_const)"

value "show_acom_opt (AI_const test2_const)"
value "show_acom_opt (AI_const test3_const)"

value "show_acom (steps test4_const 0)"
value "show_acom (steps test4_const 1)"
value "show_acom (steps test4_const 2)"
value "show_acom (steps test4_const 3)"
value "show_acom_opt (AI_const test4_const)"

value "show_acom (steps test5_const 0)"
value "show_acom (steps test5_const 1)"
value "show_acom (steps test5_const 2)"
value "show_acom (steps test5_const 3)"
value "show_acom (steps test5_const 4)"
value "show_acom (steps test5_const 5)"
value "show_acom_opt (AI_const test5_const)"

value "show_acom (steps test6_const 0)"
value "show_acom (steps test6_const 1)"
value "show_acom (steps test6_const 2)"
value "show_acom (steps test6_const 3)"
value "show_acom (steps test6_const 4)"
value "show_acom (steps test6_const 5)"
value "show_acom (steps test6_const 6)"
value "show_acom (steps test6_const 7)"
value "show_acom (steps test6_const 8)"
value "show_acom (steps test6_const 9)"
value "show_acom (steps test6_const 10)"
value "show_acom (steps test6_const 11)"
value "show_acom_opt (AI_const test6_const)"


text{* Monotonicity: *}

interpretation Abs_Int_mono
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
proof
  case goal1 thus ?case
    by(auto simp: plus_const_cases split: const.split)
qed

text{* Termination: *}

definition "m_const x = (case x of Const _ \<Rightarrow> 1 | Any \<Rightarrow> 0)"

interpretation Abs_Int_measure
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
and m = m_const and h = "2"
proof
  case goal1 thus ?case by(auto simp: m_const_def split: const.splits)
next
  case goal2 thus ?case by(auto simp: m_const_def split: const.splits)
next
  case goal3 thus ?case by(auto simp: m_const_def split: const.splits)
qed

thm AI_Some_measure

end
