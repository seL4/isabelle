(*  Title:      Codatatype_Examples/Misc_Data.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Miscellaneous datatype declarations.
*)

header {* Miscellaneous Datatype Declarations *}

theory Misc_Data
imports "../Codatatype"
begin

data_raw simple: 'a = "unit + unit + unit + unit"

data_raw mylist: 'list = "unit + 'a \<times> 'list"

data_raw some_passive: 'a = "'a + 'b + 'c + 'd + 'e"

data_raw lambda:
  'trm = "string +
          'trm \<times> 'trm +
          string \<times> 'trm +
          (string \<times> 'trm) fset \<times> 'trm"

data_raw par_lambda:
  'trm = "'a +
          'trm \<times> 'trm +
          'a \<times> 'trm +
          ('a \<times> 'trm) fset \<times> 'trm"

(*
  ('a, 'b1, 'b2) F1 = 'a * 'b1 + 'a * 'b2
  ('a, 'b1, 'b2) F2 = unit + 'b1 * 'b2
*)

data_raw F1: 'b1 = "'a \<times> 'b1 + 'a \<times> 'b2"
and F2: 'b2 = "unit + 'b1 * 'b2"

(*
  'a tree = Empty | Node of 'a * 'a forest      ('b = unit + 'a * 'c)
  'a forest = Nil | Cons of 'a tree * 'a forest ('c = unit + 'b * 'c)
*)

data_raw tree: 'tree = "unit + 'a \<times> 'forest"
and forest: 'forest = "unit + 'tree \<times> 'forest"

(*
  'a tree = Empty | Node of 'a branch * 'a branch ('b = unit + 'c * 'c)
'  a branch = Branch of 'a * 'a tree              ('c = 'a * 'b)
*)

data_raw tree': 'tree = "unit + 'branch \<times> 'branch"
and branch: 'branch = "'a \<times> 'tree"

(*
  exp = Sum of term * exp          ('c = 'd + 'd * 'c)
  term = Prod of factor * term     ('d = 'e + 'e * 'd)
  factor = C 'a | V 'b | Paren exp ('e = 'a + 'b + 'c)
*)

data_raw EXPR: 'E = "'T + 'T \<times> 'E"
and TERM: 'T = "'F + 'F \<times> 'T"
and FACTOR: 'F = "'a + 'b + 'E"

data_raw some_killing: 'a = "'b \<Rightarrow> 'd \<Rightarrow> ('a + 'c)"
and in_here: 'c = "'d \<times> 'b + 'e"

data_raw nofail1: 'a = "'a \<times> 'b + 'b"
data_raw nofail2: 'a = "('a \<times> 'b \<times> 'a \<times> 'b) list"
data_raw nofail3: 'a = "'b \<times> ('a \<times> 'b \<times> 'a \<times> 'b) fset"
data_raw nofail4: 'a = "('a \<times> ('a \<times> 'b \<times> 'a \<times> 'b) fset) list"

(*
data_raw fail: 'a = "'a \<times> 'b \<times> 'a \<times> 'b list"
data_raw fail: 'a = "'a \<times> 'b \<times> 'a \<times> 'b"
data_raw fail: 'a = "'a \<times> 'b + 'a"
data_raw fail: 'a = "'a \<times> 'b"
*)

data_raw L1: 'L1 = "'L2 list"
and L2: 'L2 = "'L1 fset + 'L2"

data_raw K1: 'K1 = "'K2"
and K2: 'K2 = "'K3"
and K3: 'K3 = "'K1 list"

data_raw t1: 't1 = "'t3 + 't2"
and t2: 't2 = "'t1"
and t3: 't3 = "unit"

data_raw t1': 't1 = "'t2 + 't3"
and t2': 't2 = "'t1"
and t3': 't3 = "unit"

(*
data_raw fail1: 'L1 = "'L2"
and fail2: 'L2 = "'L3"
and fail2: 'L3 = "'L1"

data_raw fail1: 'L1 = "'L2 list \<times> 'L2"
and fail2: 'L2 = "'L2 fset \<times> 'L3"
and fail2: 'L3 = "'L1"

data_raw fail1: 'L1 = "'L2 list \<times> 'L2"
and fail2: 'L2 = "'L1 fset \<times> 'L1"
*)
(* SLOW
data_raw K1': 'K1 = "'K2 + 'a list"
and K2': 'K2 = "'K3 + 'c fset"
and K3': 'K3 = "'K3 + 'K4 + 'K4 \<times> 'K5"
and K4': 'K4 = "'K5 + 'a list list list"
and K5': 'K5 = "'K6"
and K6': 'K6 = "'K7"
and K7': 'K7 = "'K8"
and K8': 'K8 = "'K1 list"

(*time comparison*)
datatype ('a, 'c) D1 = A1 "('a, 'c) D2" | B1 "'a list"
     and ('a, 'c) D2 = A2 "('a, 'c) D3" | B2 "'c list"
     and ('a, 'c) D3 = A3 "('a, 'c) D3" | B3 "('a, 'c) D4" | C3 "('a, 'c) D4" "('a, 'c) D5"
     and ('a, 'c) D4 = A4 "('a, 'c) D5" | B4 "'a list list list"
     and ('a, 'c) D5 = A5 "('a, 'c) D6"
     and ('a, 'c) D6 = A6 "('a, 'c) D7"
     and ('a, 'c) D7 = A7 "('a, 'c) D8"
     and ('a, 'c) D8 = A8 "('a, 'c) D1 list"
*)

(* fail:
data_raw t1: 't1 = "'t2 * 't3 + 't2 * 't4"
and t2: 't2 = "unit"
and t3: 't3 = 't4
and t4: 't4 = 't1
*)

data_raw k1: 'k1 = "'k2 * 'k3 + 'k2 * 'k4"
and k2: 'k2 = unit
and k3: 'k3 = 'k4
and k4: 'k4 = unit

data_raw tt1: 'tt1 = "'tt3 * 'tt2 + 'tt2 * 'tt4"
and tt2: 'tt2 = unit
and tt3: 'tt3 = 'tt1
and tt4: 'tt4 = unit
(* SLOW
data_raw s1: 's1 = "'s2 * 's3 * 's4 + 's3 + 's2 * 's6 + 's4 * 's2 + 's2 * 's2"
and s2: 's2 = "'s7 * 's5 + 's5 * 's4 * 's6"
and s3: 's3 = "'s1 * 's7 * 's2 + 's3 * 's3 + 's4 * 's5"
and s4: 's4 = 's5
and s5: 's5 = unit
and s6: 's6 = "'s6 + 's1 * 's2 + 's6"
and s7: 's7 = "'s8 + 's5"
and s8: 's8 = nat
*)

end
