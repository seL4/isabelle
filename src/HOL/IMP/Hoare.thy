(*  Title:      HOL/IMP/Hoare.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM
*)

header "Inductive Definition of Hoare Logic"

theory Hoare imports Natural begin

types assn = "state => bool"

inductive
  hoare :: "assn => com => assn => bool" ("|- ({(1_)}/ (_)/ {(1_)})" 50)
where
  skip: "|- {P}\<SKIP>{P}"
| ass:  "|- {%s. P(s[x\<mapsto>a s])} x:==a {P}"
| semi: "[| |- {P}c{Q}; |- {Q}d{R} |] ==> |- {P} c;d {R}"
| If: "[| |- {%s. P s & b s}c{Q}; |- {%s. P s & ~b s}d{Q} |] ==>
      |- {P} \<IF> b \<THEN> c \<ELSE> d {Q}"
| While: "|- {%s. P s & b s} c {P} ==>
         |- {P} \<WHILE> b \<DO> c {%s. P s & ~b s}"
| conseq: "[| !s. P' s --> P s; |- {P}c{Q}; !s. Q s --> Q' s |] ==>
          |- {P'}c{Q'}"

lemma strengthen_pre: "[| !s. P' s --> P s; |- {P}c{Q} |] ==> |- {P'}c{Q}"
by (blast intro: conseq)

lemma weaken_post: "[| |- {P}c{Q}; !s. Q s --> Q' s |] ==> |- {P}c{Q'}"
by (blast intro: conseq)

lemma While':
assumes "|- {%s. P s & b s} c {P}" and "ALL s. P s & \<not> b s \<longrightarrow> Q s"
shows "|- {P} \<WHILE> b \<DO> c {Q}"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])


lemmas [simp] = skip ass semi If

lemmas [intro!] = hoare.skip hoare.ass hoare.semi hoare.If

end
