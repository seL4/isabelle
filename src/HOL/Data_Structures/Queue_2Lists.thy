(* Author: Tobias Nipkow *)

section \<open>Queue Implementation via 2 Lists\<close>

theory Queue_2Lists
imports Queue_Spec
begin

text \<open>Definitions:\<close>

type_synonym 'a queue = "'a list \<times> 'a list"

fun norm :: "'a queue \<Rightarrow> 'a queue" where
"norm (os,is) = (if os = [] then (rev is, []) else (os,is))"

fun enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"enq a (os,is) = norm(os, a # is)"

fun deq :: "'a queue \<Rightarrow> 'a queue" where
"deq (os,is) = (if os = [] then (os,is) else norm(tl os,is))"

fun first :: "'a queue \<Rightarrow> 'a" where
"first (a # os,is) = a"

fun is_empty :: "'a queue \<Rightarrow> bool" where
"is_empty (os,is) = (os = [])"

fun list :: "'a queue \<Rightarrow> 'a list" where
"list (os,is) = os @ rev is"

fun invar :: "'a queue \<Rightarrow> bool" where
"invar (os,is) = (os = [] \<longrightarrow> is = [])"


text \<open>Implementation correctness:\<close>

interpretation Queue
where empty = "([],[])" and enq = enq and deq = deq and first = first
and is_empty = is_empty and list = list and invar = invar
proof (standard, goal_cases)
  case 1 show ?case by (simp)
next
  case (2 q) thus ?case by(cases q) (simp)
next
  case (3 q) thus ?case by(cases q) (simp)
next
  case (4 q) thus ?case by(cases q) (auto simp: neq_Nil_conv)
next
  case (5 q) thus ?case by(cases q) (auto)
next
  case 6 show ?case by(simp)
next
  case (7 q) thus ?case by(cases q) (simp)
next
  case (8 q) thus ?case by(cases q) (simp)
qed

text \<open>Running times:\<close>

fun t_norm :: "'a queue \<Rightarrow> nat" where
"t_norm (os,is) = (if os = [] then length is else 0) + 1"

fun t_enq :: "'a \<Rightarrow> 'a queue \<Rightarrow> nat" where
"t_enq a (os,is) = t_norm(os, a # is)"

fun t_deq :: "'a queue \<Rightarrow> nat" where
"t_deq (os,is) = (if os = [] then 0 else t_norm(tl os,is)) + 1"

fun t_first :: "'a queue \<Rightarrow> nat" where
"t_first (a # os,is) = 1"

fun t_is_empty :: "'a queue \<Rightarrow> nat" where
"t_is_empty (os,is) = 1"

text \<open>Amortized running times:\<close>

fun \<Phi> :: "'a queue \<Rightarrow> nat" where
"\<Phi>(os,is) = length is"

lemma a_enq: "t_enq a (os,is) + \<Phi>(enq a (os,is)) - \<Phi>(os,is) \<le> 2"
by(auto)

lemma a_deq: "t_deq (os,is) + \<Phi>(deq (os,is)) - \<Phi>(os,is) \<le> 2"
by(auto)

end
