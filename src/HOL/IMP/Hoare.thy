(*  Title:      HOL/IMP/Hoare.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM

Inductive definition of Hoare logic
*)

Hoare = Denotation +

types assn = state => bool

consts
  hoare :: "(assn * com * assn) set"
  hoare_valid :: [assn,com,assn] => bool ("|= {(1_)}/ (_)/ {(1_)}" 50)
defs
  hoare_valid_def "|= {P}c{Q} == !s t. (s,t) : C(c) --> P s --> Q t"

syntax "@hoare" :: [bool,com,bool] => bool ("|- {(1_)}/ (_)/ {(1_)}" 50)
translations "|- {P}c{Q}" == "(P,c,Q) : hoare"

inductive "hoare"
intrs
  skip "|- {P}Skip{P}"
  ass  "|- {%s.P(s[A a s/x])} x:=a {P}"
  semi "[| |- {P}c{Q}; |- {Q}d{R} |] ==> |- {P} c;d {R}"
  If "[| |- {%s. P s & B b s}c{Q}; |- {%s. P s & ~B b s}d{Q} |] ==>
      |- {P} IF b THEN c ELSE d {Q}"
  While "|- {%s. P s & B b s} c {P} ==>
         |- {P} WHILE b DO c {%s. P s & ~B b s}"
  conseq "[| !s. P' s --> P s; |- {P}c{Q}; !s. Q s --> Q' s |] ==>
          |- {P'}c{Q'}"

consts swp :: com => assn => assn
defs swp_def "swp c Q == (%s. !t. (s,t) : C(c) --> Q t)"

end
