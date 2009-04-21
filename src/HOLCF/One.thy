(*  Title:      HOLCF/One.thy
    Author:     Oscar Slotosch
*)

header {* The unit domain *}

theory One
imports Lift
begin

types one = "unit lift"
translations
  "one" <= (type) "unit lift" 

definition
  ONE :: "one"
where
  "ONE == Def ()"

text {* Exhaustion and Elimination for type @{typ one} *}

lemma Exh_one: "t = \<bottom> \<or> t = ONE"
unfolding ONE_def by (induct t) simp_all

lemma oneE: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = ONE \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding ONE_def by (induct p) simp_all

lemma one_induct: "\<lbrakk>P \<bottom>; P ONE\<rbrakk> \<Longrightarrow> P x"
by (cases x rule: oneE) simp_all

lemma dist_less_one [simp]: "\<not> ONE \<sqsubseteq> \<bottom>"
unfolding ONE_def by simp

lemma less_ONE [simp]: "x \<sqsubseteq> ONE"
by (induct x rule: one_induct) simp_all

lemma ONE_less_iff [simp]: "ONE \<sqsubseteq> x \<longleftrightarrow> x = ONE"
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
  one_when :: "'a::pcpo \<rightarrow> one \<rightarrow> 'a" where
  "one_when = (\<Lambda> a. strictify\<cdot>(\<Lambda> _. a))"

translations
  "case x of XCONST ONE \<Rightarrow> t" == "CONST one_when\<cdot>t\<cdot>x"
  "\<Lambda> (XCONST ONE). t" == "CONST one_when\<cdot>t"

lemma one_when1 [simp]: "(case \<bottom> of ONE \<Rightarrow> t) = \<bottom>"
by (simp add: one_when_def)

lemma one_when2 [simp]: "(case ONE of ONE \<Rightarrow> t) = t"
by (simp add: one_when_def)

lemma one_when3 [simp]: "(case x of ONE \<Rightarrow> ONE) = x"
by (induct x rule: one_induct) simp_all

end
