(*  Title: 	HOL/IMP/Hoare.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Inductive definition of Hoare logic
*)

Hoare = Denotation +

types assn = state => bool

consts
  hoare :: "(assn * com * assn) set"
  spec :: [state=>bool,com,state=>bool] => bool
defs
  spec_def "spec P c Q == !s t. (s,t) : C(c) --> P s --> Q t"

syntax "@hoare" :: [bool,com,bool] => bool ("{{(1_)}}/ (_)/ {{(1_)}}" 10)
translations "{{P}}c{{Q}}" == "(P,c,Q) : hoare"

inductive "hoare"
intrs
  hoare_skip "{{P}}skip{{P}}"
  hoare_ass  "{{%s.P(s[A a s/x])}} x:=a {{P}}"
  hoare_semi "[| {{P}}c{{Q}}; {{Q}}d{{R}} |] ==> {{P}} c;d {{R}}"
  hoare_if   "[| {{%s. P s & B b s}}c{{Q}}; {{%s. P s & ~B b s}}d{{Q}} |] ==>
              {{P}} ifc b then c else d {{Q}}"
  hoare_while "[| {{%s. P s & B b s}} c {{P}} |] ==>
	       {{P}} while b do c {{%s. P s & ~B b s}}"
  hoare_conseq "[| !s. P' s --> P s; {{P}}c{{Q}}; !s. Q s --> Q' s |] ==>
		{{P'}}c{{Q'}}"

end
