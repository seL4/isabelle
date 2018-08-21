(* Author: Tobias Nipkow *)

subsection "Constant Propagation"

theory Abs_Int1_const
imports Abs_Int1
begin

datatype const = Const val | Any

fun \<gamma>_const where
"\<gamma>_const (Const i) = {i}" |
"\<gamma>_const (Any) = UNIV"

fun plus_const where
"plus_const (Const i) (Const j) = Const(i+j)" |
"plus_const _ _ = Any"

lemma plus_const_cases: "plus_const a1 a2 =
  (case (a1,a2) of (Const i, Const j) \<Rightarrow> Const(i+j) | _ \<Rightarrow> Any)"
by(auto split: prod.split const.split)

instantiation const :: semilattice_sup_top
begin

fun less_eq_const where "x \<le> y = (y = Any | x=y)"

definition "x < (y::const) = (x \<le> y & \<not> y \<le> x)"

fun sup_const where "x \<squnion> y = (if x=y then x else Any)"

definition "\<top> = Any"

instance
proof (standard, goal_cases)
  case 1 thus ?case by (rule less_const_def)
next
  case (2 x) show ?case by (cases x) simp_all
next
  case (3 x y z) thus ?case by(cases z, cases y, cases x, simp_all)
next
  case (4 x y) thus ?case by(cases x, cases y, simp_all, cases y, simp_all)
next
  case (6 x y) thus ?case by(cases x, cases y, simp_all)
next
  case (5 x y) thus ?case by(cases y, cases x, simp_all)
next
  case (7 x y z) thus ?case by(cases z, cases y, cases x, simp_all)
next
  case 8 thus ?case by(simp add: top_const_def)
qed

end


global_interpretation Val_semilattice
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
proof (standard, goal_cases)
  case (1 a b) thus ?case
    by(cases a, cases b, simp, simp, cases b, simp, simp)
next
  case 2 show ?case by(simp add: top_const_def)
next
  case 3 show ?case by simp
next
  case 4 thus ?case by(auto simp: plus_const_cases split: const.split)
qed

global_interpretation Abs_Int
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
defines AI_const = AI and step_const = step' and aval'_const = aval'
..


subsubsection "Tests"

definition "steps c i = (step_const \<top> ^^ i) (bot c)"

value "show_acom (steps test1_const 0)"
value "show_acom (steps test1_const 1)"
value "show_acom (steps test1_const 2)"
value "show_acom (steps test1_const 3)"
value "show_acom (the(AI_const test1_const))"

value "show_acom (the(AI_const test2_const))"
value "show_acom (the(AI_const test3_const))"

value "show_acom (steps test4_const 0)"
value "show_acom (steps test4_const 1)"
value "show_acom (steps test4_const 2)"
value "show_acom (steps test4_const 3)"
value "show_acom (steps test4_const 4)"
value "show_acom (the(AI_const test4_const))"

value "show_acom (steps test5_const 0)"
value "show_acom (steps test5_const 1)"
value "show_acom (steps test5_const 2)"
value "show_acom (steps test5_const 3)"
value "show_acom (steps test5_const 4)"
value "show_acom (steps test5_const 5)"
value "show_acom (steps test5_const 6)"
value "show_acom (the(AI_const test5_const))"

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
value "show_acom (steps test6_const 12)"
value "show_acom (steps test6_const 13)"
value "show_acom (the(AI_const test6_const))"


text\<open>Monotonicity:\<close>

global_interpretation Abs_Int_mono
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
proof (standard, goal_cases)
  case 1 thus ?case by(auto simp: plus_const_cases split: const.split)
qed

text\<open>Termination:\<close>

definition m_const :: "const \<Rightarrow> nat" where
"m_const x = (if x = Any then 0 else 1)"

global_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_const and num' = Const and plus' = plus_const
and m = m_const and h = "1"
proof (standard, goal_cases)
  case 1 thus ?case by(auto simp: m_const_def split: const.splits)
next
  case 2 thus ?case by(auto simp: m_const_def less_const_def split: const.splits)
qed

thm AI_Some_measure

end
