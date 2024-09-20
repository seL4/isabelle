(*  Title:      HOL/Quickcheck_Examples/Quickcheck_Lattice_Examples.thy
    Author:     Lukas Bulwahn
    Copyright   2010 TU Muenchen
*)

theory Quickcheck_Lattice_Examples
imports Main
begin

declare [[quickcheck_finite_type_size=5]]

text \<open>We show how other default types help to find counterexamples to propositions if
  the standard default type \<^typ>\<open>int\<close> is insufficient.\<close>

notation
  less_eq  (infix \<open>\<sqsubseteq>\<close> 50) and
  less  (infix \<open>\<sqsubset>\<close> 50) and
  top (\<open>\<top>\<close>) and
  bot (\<open>\<bottom>\<close>) and
  inf (infixl \<open>\<sqinter>\<close> 70) and
  sup (infixl \<open>\<squnion>\<close> 65)

declare [[quickcheck_narrowing_active = false, quickcheck_timeout = 3600]]

subsection \<open>Distributive lattices\<close>

lemma sup_inf_distrib2:
 "((y :: 'a :: distrib_lattice) \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  quickcheck[expect = no_counterexample]
by(simp add: inf_sup_aci sup_inf_distrib1)

lemma sup_inf_distrib2_1:
 "((y :: 'a :: lattice) \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  quickcheck[expect = counterexample]
  oops

lemma sup_inf_distrib2_2:
 "((y :: 'a :: distrib_lattice) \<sqinter> z') \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  quickcheck[expect = counterexample]
  oops

lemma inf_sup_distrib1_1:
 "(x :: 'a :: distrib_lattice) \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x' \<sqinter> z)"
  quickcheck[expect = counterexample]
  oops

lemma inf_sup_distrib2_1:
 "((y :: 'a :: distrib_lattice) \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (y \<sqinter> x)"
  quickcheck[expect = counterexample]
  oops

subsection \<open>Bounded lattices\<close>

lemma inf_bot_left [simp]:
  "\<bottom> \<sqinter> (x :: 'a :: bounded_lattice_bot) = \<bottom>"
  quickcheck[expect = no_counterexample]
  by (rule inf_absorb1) simp

lemma inf_bot_left_1:
  "\<bottom> \<sqinter> (x :: 'a :: bounded_lattice_bot) = x"
  quickcheck[expect = counterexample]
  oops

lemma inf_bot_left_2:
  "y \<sqinter> (x :: 'a :: bounded_lattice_bot) = \<bottom>"
  quickcheck[expect = counterexample]
  oops

lemma inf_bot_left_3:
  "x \<noteq> \<bottom> ==> y \<sqinter> (x :: 'a :: bounded_lattice_bot) \<noteq> \<bottom>"
  quickcheck[expect = counterexample]
  oops

lemma inf_bot_right [simp]:
  "(x :: 'a :: bounded_lattice_bot) \<sqinter> \<bottom> = \<bottom>"
  quickcheck[expect = no_counterexample]
  by (rule inf_absorb2) simp

lemma inf_bot_right_1:
  "x \<noteq> \<bottom> ==> (x :: 'a :: bounded_lattice_bot) \<sqinter> \<bottom> = y"
  quickcheck[expect = counterexample]
  oops

lemma inf_bot_right_2:
  "(x :: 'a :: bounded_lattice_bot) \<sqinter> \<bottom> ~= \<bottom>"
  quickcheck[expect = counterexample]
  oops

lemma sup_bot_right [simp]:
  "(x :: 'a :: bounded_lattice_bot) \<squnion> \<bottom> = \<bottom>"
  quickcheck[expect = counterexample]
  oops

lemma sup_bot_left [simp]:
  "\<bottom> \<squnion> (x :: 'a :: bounded_lattice_bot) = x"
  quickcheck[expect = no_counterexample]
  by (rule sup_absorb2) simp

lemma sup_bot_right_2 [simp]:
  "(x :: 'a :: bounded_lattice_bot) \<squnion> \<bottom> = x"
  quickcheck[expect = no_counterexample]
  by (rule sup_absorb1) simp

lemma sup_eq_bot_iff [simp]:
  "(x :: 'a :: bounded_lattice_bot) \<squnion> y = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  quickcheck[expect = no_counterexample]
  by (simp add: eq_iff)

lemma sup_top_left [simp]:
  "\<top> \<squnion> (x :: 'a :: bounded_lattice_top) = \<top>"
  quickcheck[expect = no_counterexample]
  by (rule sup_absorb1) simp

lemma sup_top_right [simp]:
  "(x :: 'a :: bounded_lattice_top) \<squnion> \<top> = \<top>"
  quickcheck[expect = no_counterexample]
  by (rule sup_absorb2) simp

lemma inf_top_left [simp]:
  "\<top> \<sqinter> x = (x :: 'a :: bounded_lattice_top)"
  quickcheck[expect = no_counterexample]
  by (rule inf_absorb2) simp

lemma inf_top_right [simp]:
  "x \<sqinter> \<top> = (x :: 'a :: bounded_lattice_top)"
  quickcheck[expect = no_counterexample]
  by (rule inf_absorb1) simp

lemma inf_eq_top_iff [simp]:
  "(x :: 'a :: bounded_lattice_top) \<sqinter> y = \<top> \<longleftrightarrow> x = \<top> \<and> y = \<top>"
  quickcheck[expect = no_counterexample]
  by (simp add: eq_iff)


no_notation
  less_eq  (infix \<open>\<sqsubseteq>\<close> 50) and
  less (infix \<open>\<sqsubset>\<close> 50) and
  inf  (infixl \<open>\<sqinter>\<close> 70) and
  sup  (infixl \<open>\<squnion>\<close> 65) and
  top (\<open>\<top>\<close>) and
  bot (\<open>\<bottom>\<close>)

end
