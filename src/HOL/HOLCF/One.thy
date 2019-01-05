(*  Title:      HOL/HOLCF/One.thy
    Author:     Oscar Slotosch
*)

section \<open>The unit domain\<close>

theory One
  imports Lift
begin

type_synonym one = "unit lift"

translations
  (type) "one" \<leftharpoondown> (type) "unit lift"

definition ONE :: "one"
  where "ONE \<equiv> Def ()"

text \<open>Exhaustion and Elimination for type \<^typ>\<open>one\<close>\<close>

lemma Exh_one: "t = \<bottom> \<or> t = ONE"
  by (induct t) (simp_all add: ONE_def)

lemma oneE [case_names bottom ONE]: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = ONE \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (induct p) (simp_all add: ONE_def)

lemma one_induct [case_names bottom ONE]: "P \<bottom> \<Longrightarrow> P ONE \<Longrightarrow> P x"
  by (cases x rule: oneE) simp_all

lemma dist_below_one [simp]: "ONE \<notsqsubseteq> \<bottom>"
  by (simp add: ONE_def)

lemma below_ONE [simp]: "x \<sqsubseteq> ONE"
  by (induct x rule: one_induct) simp_all

lemma ONE_below_iff [simp]: "ONE \<sqsubseteq> x \<longleftrightarrow> x = ONE"
  by (induct x rule: one_induct) simp_all

lemma ONE_defined [simp]: "ONE \<noteq> \<bottom>"
  by (simp add: ONE_def)

lemma one_neq_iffs [simp]:
  "x \<noteq> ONE \<longleftrightarrow> x = \<bottom>"
  "ONE \<noteq> x \<longleftrightarrow> x = \<bottom>"
  "x \<noteq> \<bottom> \<longleftrightarrow> x = ONE"
  "\<bottom> \<noteq> x \<longleftrightarrow> x = ONE"
  by (induct x rule: one_induct) simp_all

lemma compact_ONE: "compact ONE"
  by (rule compact_chfin)

text \<open>Case analysis function for type \<^typ>\<open>one\<close>\<close>

definition one_case :: "'a::pcpo \<rightarrow> one \<rightarrow> 'a"
  where "one_case = (\<Lambda> a x. seq\<cdot>x\<cdot>a)"

translations
  "case x of XCONST ONE \<Rightarrow> t" \<rightleftharpoons> "CONST one_case\<cdot>t\<cdot>x"
  "case x of XCONST ONE :: 'a \<Rightarrow> t" \<rightharpoonup> "CONST one_case\<cdot>t\<cdot>x"
  "\<Lambda> (XCONST ONE). t" \<rightleftharpoons> "CONST one_case\<cdot>t"

lemma one_case1 [simp]: "(case \<bottom> of ONE \<Rightarrow> t) = \<bottom>"
  by (simp add: one_case_def)

lemma one_case2 [simp]: "(case ONE of ONE \<Rightarrow> t) = t"
  by (simp add: one_case_def)

lemma one_case3 [simp]: "(case x of ONE \<Rightarrow> ONE) = x"
  by (induct x rule: one_induct) simp_all

end
