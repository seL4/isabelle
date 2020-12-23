(*  Title:      HOL/Hoare/Hoare_Syntax.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Author:     Walter Guttmann (extension to total-correctness proofs)
*)

section \<open>Concrete syntax for Hoare logic, with translations for variables\<close>

theory Hoare_Syntax
  imports Main
begin

syntax
  "_assign" :: "idt \<Rightarrow> 'b \<Rightarrow> 'com"  ("(2_ :=/ _)" [70, 65] 61)
  "_Seq" :: "'com \<Rightarrow> 'com \<Rightarrow> 'com"  ("(_;/ _)" [61,60] 60)
  "_Cond" :: "'bexp \<Rightarrow> 'com \<Rightarrow> 'com \<Rightarrow> 'com"  ("(1IF _/ THEN _ / ELSE _/ FI)" [0,0,0] 61)
  "_While" :: "'bexp \<Rightarrow> 'assn \<Rightarrow> 'var \<Rightarrow> 'com \<Rightarrow> 'com"  ("(1WHILE _/ INV {_} / VAR {_} //DO _ /OD)" [0,0,0,0] 61)

syntax
  "_While0" :: "'bexp \<Rightarrow> 'assn \<Rightarrow> 'com \<Rightarrow> 'com"  ("(1WHILE _/ INV {_} //DO _ /OD)" [0,0,0] 61)
translations
  "WHILE b INV {x} DO c OD" \<rightharpoonup> "WHILE b INV {x} VAR {0} DO c OD"

syntax
 "_hoare_vars" :: "[idts, 'assn,'com, 'assn] \<Rightarrow> bool"  ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
 "_hoare_vars_tc" :: "[idts, 'assn, 'com, 'assn] \<Rightarrow> bool"  ("VARS _// [_] // _ // [_]" [0,0,55,0] 50)
syntax (output)
 "_hoare" :: "['assn, 'com, 'assn] \<Rightarrow> bool"  ("{_} // _ // {_}" [0,55,0] 50)
 "_hoare_tc" :: "['assn, 'com, 'assn] \<Rightarrow> bool"  ("[_] // _ // [_]" [0,55,0] 50)

ML_file \<open>hoare_syntax.ML\<close>

end
