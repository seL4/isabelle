(*  Title: 	HOL/IMP/Hoare.thy
    ID:         $$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Semantic embedding of Hoare logic
*)

Hoare = Denotation +
consts
  spec:: "[state=>bool,com,state=>bool] => bool" ("{{(1_)}}/ (_)/ {{(1_)}}" 10)
defs
  spec_def "spec P c Q == !s t. <s,t> : C(c) --> P s --> Q t"
end
