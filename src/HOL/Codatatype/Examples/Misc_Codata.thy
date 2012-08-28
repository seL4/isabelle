(*  Title:      Codatatype_Examples/Misc_Data.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Miscellaneous codatatype declarations.
*)

header {* Miscellaneous Codatatype Declarations *}

theory Misc_Codata
imports "../Codatatype/Codatatype"
begin

ML {* quick_and_dirty := false *}

ML {* PolyML.fullGC (); *}

bnf_codata simple: 'a = "unit + unit + unit + unit"

bnf_codata stream: 's = "'a \<times> 's"

bnf_codata llist: 'llist = "unit + 'a \<times> 'llist"

bnf_codata some_passive: 'a = "'a + 'b + 'c + 'd + 'e"

(*
  ('a, 'b1, 'b2) F1 = 'a * 'b1 + 'a * 'b2
  ('a, 'b1, 'b2) F2 = unit + 'b1 * 'b2
*)

bnf_codata F1: 'b1 = "'a \<times> 'b1 + 'a \<times> 'b2"
and F2: 'b2 = "unit + 'b1 * 'b2"

bnf_codata EXPR:   'E = "'T + 'T \<times> 'E"
and TERM:   'T = "'F + 'F \<times> 'T"
and FACTOR: 'F = "'a + 'b + 'E"

bnf_codata llambda:
  'trm = "string +
          'trm \<times> 'trm +
          string \<times> 'trm +
          (string \<times> 'trm) fset \<times> 'trm"

bnf_codata par_llambda:
  'trm = "'a +
          'trm \<times> 'trm +
          'a \<times> 'trm +
          ('a \<times> 'trm) fset \<times> 'trm"

(*
  'a tree = Empty | Node of 'a * 'a forest      ('b = unit + 'a * 'c)
  'a forest = Nil | Cons of 'a tree * 'a forest ('c = unit + 'b * 'c)
*)

bnf_codata tree:     'tree = "unit + 'a \<times> 'forest"
and forest: 'forest = "unit + 'tree \<times> 'forest"

bnf_codata CPS: 'a = "'b + 'b \<Rightarrow> 'a"

bnf_codata fun_rhs: 'a = "'b1 \<Rightarrow> 'b2 \<Rightarrow> 'b3 \<Rightarrow> 'b4 \<Rightarrow> 'b5 \<Rightarrow> 'b6 \<Rightarrow> 'b7 \<Rightarrow> 'b8 \<Rightarrow> 'b9 \<Rightarrow> 'a"

bnf_codata fun_rhs': 'a = "'b1 \<Rightarrow> 'b2 \<Rightarrow> 'b3 \<Rightarrow> 'b4 \<Rightarrow> 'b5 \<Rightarrow> 'b6 \<Rightarrow> 'b7 \<Rightarrow> 'b8 \<Rightarrow> 'b9 \<Rightarrow> 'b10 \<Rightarrow>
                    'b11 \<Rightarrow> 'b12 \<Rightarrow> 'b13 \<Rightarrow> 'b14 \<Rightarrow> 'b15 \<Rightarrow> 'b16 \<Rightarrow> 'b17 \<Rightarrow> 'b18 \<Rightarrow> 'b19 \<Rightarrow> 'b20 \<Rightarrow> 'a"

bnf_codata some_killing: 'a = "'b \<Rightarrow> 'd \<Rightarrow> ('a + 'c)"
and in_here: 'c = "'d \<times> 'b + 'e"

bnf_codata some_killing': 'a = "'b \<Rightarrow> 'd \<Rightarrow> ('a + 'c)"
and in_here': 'c = "'d + 'e"

bnf_codata some_killing'': 'a = "'b \<Rightarrow> 'c"
and in_here'': 'c = "'d \<times> 'b + 'e"

bnf_codata less_killing: 'a = "'b \<Rightarrow> 'c"

(* SLOW, MEMORY-HUNGRY
bnf_codata K1': 'K1 = "'K2 + 'a list"
and K2': 'K2 = "'K3 + 'c fset"
and K3': 'K3 = "'K3 + 'K4 + 'K4 \<times> 'K5"
and K4': 'K4 = "'K5 + 'a list list list"
and K5': 'K5 = "'K6"
and K6': 'K6 = "'K7"
and K7': 'K7 = "'K8"
and K8': 'K8 = "'K1 list"
*)

end
