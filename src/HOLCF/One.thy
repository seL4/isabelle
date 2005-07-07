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

end
