(*  Title:      HOL/MicroJava/J/Conform.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Conformity relations for type safety of Java
*)

Conform = State +

constdefs

  hext :: "aheap \\<Rightarrow> aheap \\<Rightarrow> bool"		 (     "_\\<le>|_"  [51,51] 50)
 "h\\<le>|h' \\<equiv> \\<forall>a C fs. h a = Some(C,fs) \\<longrightarrow> (\\<exists>fs'. h' a = Some(C,fs'))"

  conf :: "'c prog \\<Rightarrow> aheap \\<Rightarrow> val \\<Rightarrow> ty \\<Rightarrow> bool"	 ( "_,_\\<turnstile>_\\<Colon>\\<preceq>_"  [51,51,51,51] 50)
 "G,h\\<turnstile>v\\<Colon>\\<preceq>T \\<equiv> \\<exists>T'. typeof (option_map obj_ty o h) v = Some T' \\<and> G\\<turnstile>T'\\<preceq>T"

  lconf :: "'c prog \\<Rightarrow> aheap \\<Rightarrow> ('a \\<leadsto> val) \\<Rightarrow> ('a \\<leadsto> ty) \\<Rightarrow> bool"
                                                 ("_,_\\<turnstile>_[\\<Colon>\\<preceq>]_" [51,51,51,51] 50)
 "G,h\\<turnstile>vs[\\<Colon>\\<preceq>]Ts \\<equiv> \\<forall>n T. Ts n = Some T \\<longrightarrow> (\\<exists>v. vs n = Some v \\<and> G,h\\<turnstile>v\\<Colon>\\<preceq>T)"

  oconf :: "'c prog \\<Rightarrow> aheap \\<Rightarrow> obj \\<Rightarrow> bool"      ("_,_\\<turnstile>_\\<surd>"     [51,51,51]    50)
 "G,h\\<turnstile>obj\\<surd> \\<equiv> G,h\\<turnstile>snd obj[\\<Colon>\\<preceq>]map_of (fields (G,fst obj))"

  hconf :: "'c prog \\<Rightarrow> aheap \\<Rightarrow> bool"             ("_\\<turnstile>h _\\<surd>"      [51,51]       50)
 "G\\<turnstile>h h\\<surd>    \\<equiv> \\<forall>a obj. h a = Some obj \\<longrightarrow> G,h\\<turnstile>obj\\<surd>"

  conforms :: "state \\<Rightarrow> java_mb env \\<Rightarrow> bool"	 ("_\\<Colon>\\<preceq>_"       [51,51]       50)
 "s\\<Colon>\\<preceq>E \\<equiv> prg E\\<turnstile>h heap s\\<surd> \\<and> prg E,heap s\\<turnstile>locals s[\\<Colon>\\<preceq>]localT E"

end
