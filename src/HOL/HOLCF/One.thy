(*  Title:      HOL/HOLCF/One.thy
    Author:     Oscar Slotosch
*)

header {* The unit domain *}

theory One
imports Lift
begin

type_synonym
  one = "unit lift"

translations
  (type) "one" <= (type) "unit lift"

definition ONE :: "one"
  where "ONE == Def ()"

text {* Exhaustion and Elimination for type @{typ one} *}

lemma Exh_one: "t = \<bottom> \<or> t = ONE"
unfolding ONE_def by (induct t) simp_all

lemma oneE [case_names bottom ONE]: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = ONE \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding ONE_def by (induct p) simp_all

lemma one_induct [case_names bottom ONE]: "\<lbrakk>P \<bottom>; P ONE\<rbrakk> \<Longrightarrow> P x"
by (cases x rule: oneE) simp_all

lemma dist_below_one [simp]: "ONE \<notsqsubseteq> \<bottom>"
unfolding ONE_def by simp

lemma below_ONE [simp]: "x \<sqsubseteq> ONE"
by (induct x rule: one_induct) simp_all

lemma ONE_below_iff [simp]: "ONE \<sqsubseteq> x \<longleftrightarrow> x = ONE"
by (induct x rule: one_induct) simp_all

lemma ONE_defined [simp]: "ONE \<noteq> \<bottom>"
unfolding ONE_def by simp

lemma one_neq_iffs [simp]:
  "x \<noteq> ONE \<longleftrightarrow> x = \<bottom>"
  "ONE \<noteq> x \<longleftrightarrow> x = \<bottom>"
  "x \<noteq> \<bottom> \<longleftrightarrow> x = ONE"
  "\<bottom> \<noteq> x \<longleftrightarrow> x = ONE"
by (induct x rule: one_induct) simp_all

lemma compact_ONE: "compact ONE"
by (rule compact_chfin)

text {* Case analysis function for type @{typ one} *}

definition
  one_case :: "'a::pcpo \<rightarrow> one \<rightarrow> 'a" where
  "one_case = (\<Lambda> a x. seq\<cdot>x\<cdot>a)"

translations
  "case x of XCONST ONE \<Rightarrow> t" == "CONST one_case\<cdot>t\<cdot>x"
  "case x of XCONST ONE :: 'a \<Rightarrow> t" => "CONST one_case\<cdot>t\<cdot>x"
  "\<Lambda> (XCONST ONE). t" == "CONST one_case\<cdot>t"

lemma one_case1 [simp]: "(case \<bottom> of ONE \<Rightarrow> t) = \<bottom>"
by (simp add: one_case_def)

lemma one_case2 [simp]: "(case ONE of ONE \<Rightarrow> t) = t"
by (simp add: one_case_def)

lemma one_case3 [simp]: "(case x of ONE \<Rightarrow> ONE) = x"
by (induct x rule: one_induct) simp_all

end
