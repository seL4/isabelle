(*  Title:      HOL/MicroJava/J/Conform.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Conformity relations for type safety of Java
*)

Conform = State + WellType +

types	'c env_ = "'c prog \\<times> (vname \\<leadsto> ty)" (* same as env of WellType.thy *)

constdefs

  hext :: "aheap => aheap => bool" ("_ \\<le>| _" [51,51] 50)
 "h\\<le>|h' == \\<forall>a C fs. h a = Some(C,fs) --> (\\<exists>fs'. h' a = Some(C,fs'))"

  conf :: "'c prog => aheap => val => ty => bool"	("_,_ \\<turnstile> _ ::\\<preceq> _" [51,51,51,51] 50)
 "G,h\\<turnstile>v::\\<preceq>T == \\<exists>T'. typeof (option_map obj_ty o h) v = Some T' \\<and> G\\<turnstile>T'\\<preceq>T"

  lconf :: "'c prog => aheap => ('a \\<leadsto> val) => ('a \\<leadsto> ty) => bool"
                                                ("_,_ \\<turnstile> _ [::\\<preceq>] _" [51,51,51,51] 50)
 "G,h\\<turnstile>vs[::\\<preceq>]Ts == \\<forall>n T. Ts n = Some T --> (\\<exists>v. vs n = Some v \\<and> G,h\\<turnstile>v::\\<preceq>T)"

  oconf :: "'c prog => aheap => obj => bool" ("_,_ \\<turnstile> _ \\<surd>" [51,51,51] 50)
 "G,h\\<turnstile>obj\\<surd> == G,h\\<turnstile>snd obj[::\\<preceq>]map_of (fields (G,fst obj))"

  hconf :: "'c prog => aheap => bool" ("_ \\<turnstile>h _ \\<surd>" [51,51] 50)
 "G\\<turnstile>h h\\<surd>    == \\<forall>a obj. h a = Some obj --> G,h\\<turnstile>obj\\<surd>"

  conforms :: "state => java_mb env_ => bool"	("_ ::\\<preceq> _" [51,51] 50)
 "s::\\<preceq>E == prg E\\<turnstile>h heap s\\<surd> \\<and> prg E,heap s\\<turnstile>locals s[::\\<preceq>]localT E"


syntax (HTML)
  hext     :: "aheap => aheap => bool"
              ("_ <=| _" [51,51] 50)

  conf     :: "'c prog => aheap => val => ty => bool"
              ("_,_ |- _ ::<= _"  [51,51,51,51] 50)

  lconf    :: "'c prog => aheap => ('a \\<leadsto> val) => ('a \\<leadsto> ty) => bool"
              ("_,_ |- _ [::<=] _" [51,51,51,51] 50)

  oconf    :: "'c prog => aheap => obj => bool"
              ("_,_ |- _ [ok]" [51,51,51] 50)

  hconf    :: "'c prog => aheap => bool"
              ("_ |-h _ [ok]" [51,51] 50)

  conforms :: "state => java_mb env_ => bool"
              ("_ ::<= _" [51,51] 50)

end
