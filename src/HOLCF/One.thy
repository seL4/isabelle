(*  Title:      HOLCF/One.thy
    ID:         $Id$
    Author:     Oscar Slotosch

The unit domain.
*)

header {* The unit domain *}

theory One
imports Lift
begin

types one = "unit lift"

constdefs
  ONE :: "one"
  "ONE \<equiv> Def ()"

translations
  "one" <= (type) "unit lift" 

text {* Exhaustion and Elimination for type @{typ one} *}

lemma Exh_one: "t = \<bottom> \<or> t = ONE"
apply (unfold ONE_def)
apply (induct t)
apply simp
apply simp
done

lemma oneE: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = ONE \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (rule Exh_one [THEN disjE])
apply fast
apply fast
done

lemma dist_less_one [simp]: "\<not> ONE \<sqsubseteq> \<bottom>"
apply (unfold ONE_def)
apply simp
done

lemma dist_eq_one [simp]: "ONE \<noteq> \<bottom>" "\<bottom> \<noteq> ONE"
apply (unfold ONE_def)
apply simp_all
done

lemma compact_ONE [simp]: "compact ONE"
by (rule compact_chfin)

text {* Case analysis function for type @{typ one} *}

constdefs
  one_when :: "'a::pcpo \<rightarrow> one \<rightarrow> 'a"
  "one_when \<equiv> \<Lambda> a. strictify\<cdot>(\<Lambda> _. a)"

translations
  "case x of ONE \<Rightarrow> t" == "one_when\<cdot>t\<cdot>x"
  "\<Lambda> ONE. t" == "one_when\<cdot>t"

lemma one_when1 [simp]: "(case \<bottom> of ONE \<Rightarrow> t) = \<bottom>"
by (simp add: one_when_def)

lemma one_when2 [simp]: "(case ONE of ONE \<Rightarrow> t) = t"
by (simp add: one_when_def)

lemma one_when3 [simp]: "(case x of ONE \<Rightarrow> ONE) = x"
by (rule_tac p=x in oneE, simp_all)

end
