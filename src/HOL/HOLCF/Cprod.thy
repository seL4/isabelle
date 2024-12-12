(*  Title:      HOL/HOLCF/Cprod.thy
    Author:     Franz Regensburger
*)

section \<open>The cpo of cartesian products\<close>

theory Cprod
  imports Cfun
begin

subsection \<open>Continuous case function for unit type\<close>

definition unit_when :: "'a \<rightarrow> unit \<rightarrow> 'a"
  where "unit_when = (\<Lambda> a _. a)"

translations
  "\<Lambda>(). t" \<rightleftharpoons> "CONST unit_when\<cdot>t"

lemma unit_when [simp]: "unit_when\<cdot>a\<cdot>u = a"
  by (simp add: unit_when_def)


subsection \<open>Continuous version of split function\<close>

definition csplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a \<times> 'b) \<rightarrow> 'c"
  where "csplit = (\<Lambda> f p. f\<cdot>(fst p)\<cdot>(snd p))"

translations
  "\<Lambda>(CONST Pair x y). t" \<rightleftharpoons> "CONST csplit\<cdot>(\<Lambda> x y. t)"

abbreviation cfst :: "'a \<times> 'b \<rightarrow> 'a"
  where "cfst \<equiv> Abs_cfun fst"

abbreviation csnd :: "'a \<times> 'b \<rightarrow> 'b"
  where "csnd \<equiv> Abs_cfun snd"


subsection \<open>Convert all lemmas to the continuous versions\<close>

lemma csplit1 [simp]: "csplit\<cdot>f\<cdot>\<bottom> = f\<cdot>\<bottom>\<cdot>\<bottom>"
  by (simp add: csplit_def)

lemma csplit_Pair [simp]: "csplit\<cdot>f\<cdot>(x, y) = f\<cdot>x\<cdot>y"
  by (simp add: csplit_def)

end
