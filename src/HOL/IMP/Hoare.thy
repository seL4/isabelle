(*  Title:      HOL/IMP/Hoare.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM

Inductive definition of Hoare logic
*)

Hoare = Denotation + Gfp +

types assn = state => bool

constdefs hoare_valid :: [assn,com,assn] => bool ("|= {(1_)}/ (_)/ {(1_)}" 50)
          "|= {P}c{Q} == !s t. (s,t) : C(c) --> P s --> Q t"

consts hoare :: "(assn * com * assn) set"
syntax "@hoare" :: [bool,com,bool] => bool ("|- ({(1_)}/ (_)/ {(1_)})" 50)
translations "|- {P}c{Q}" == "(P,c,Q) : hoare"

inductive hoare
intrs
  skip "|- {P}SKIP{P}"
  ass  "|- {%s.P(s[a s/x])} x:=a {P}"
  semi "[| |- {P}c{Q}; |- {Q}d{R} |] ==> |- {P} c;d {R}"
  If "[| |- {%s. P s & b s}c{Q}; |- {%s. P s & ~b s}d{Q} |] ==>
      |- {P} IF b THEN c ELSE d {Q}"
  While "|- {%s. P s & b s} c {P} ==>
         |- {P} WHILE b DO c {%s. P s & ~b s}"
  conseq "[| !s. P' s --> P s; |- {P}c{Q}; !s. Q s --> Q' s |] ==>
          |- {P'}c{Q'}"

constdefs wp :: com => assn => assn
          "wp c Q == (%s. !t. (s,t) : C(c) --> Q t)"

end
