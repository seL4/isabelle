(*  Title:      HOL/BNF_Examples/Misc_Datatype.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Miscellaneous datatype definitions.
*)

header {* Miscellaneous Datatype Definitions *}

theory Misc_Datatype
imports "~~/src/HOL/Library/Countable" "~~/src/HOL/Library/FSet"
begin

datatype_new (discs_sels) simple = X1 | X2 | X3 | X4

datatype_new (discs_sels) simple' = X1' unit | X2' unit | X3' unit | X4' unit

datatype_new (discs_sels) simple'' = X1'' nat int | X2''

datatype_new (discs_sels) 'a mylist = MyNil | MyCons (myhd: 'a) (mytl: "'a mylist")

datatype_new (discs_sels) ('b, 'c, 'd, 'e) some_passive =
  SP1 "('b, 'c, 'd, 'e) some_passive" | SP2 'b | SP3 'c | SP4 'd | SP5 'e

datatype_new (discs_sels) hfset = HFset "hfset fset"

datatype_new (discs_sels) lambda =
  Var string |
  App lambda lambda |
  Abs string lambda |
  Let "(string \<times> lambda) fset" lambda

datatype_new (discs_sels) 'a par_lambda =
  PVar 'a |
  PApp "'a par_lambda" "'a par_lambda" |
  PAbs 'a "'a par_lambda" |
  PLet "('a \<times> 'a par_lambda) fset" "'a par_lambda"

(*
  ('a, 'b1, 'b2) F1 = 'a * 'b1 + 'a * 'b2
  ('a, 'b1, 'b2) F2 = unit + 'b1 * 'b2
*)

datatype_new (discs_sels) 'a I1 = I11 'a "'a I1" | I12 'a "'a I2"
and 'a I2 = I21 | I22 "'a I1" "'a I2"

datatype_new (discs_sels) 'a tree = TEmpty | TNode 'a "'a forest"
and 'a forest = FNil | FCons "'a tree" "'a forest"

datatype_new (discs_sels) 'a tree' = TEmpty' | TNode' "'a branch" "'a branch"
and 'a branch = Branch 'a "'a tree'"

datatype_new (discs_sels) 'a bin_rose_tree = BRTree 'a "'a bin_rose_tree mylist" "'a bin_rose_tree mylist"

datatype_new (discs_sels) ('a, 'b) exp = Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) exp"
and ('a, 'b) trm = Factor "('a, 'b) factor" | Prod "('a, 'b) factor" "('a, 'b) trm"
and ('a, 'b) factor = C 'a | V 'b | Paren "('a, 'b) exp"

datatype_new (discs_sels) 'a ftree = FTLeaf 'a | FTNode "'a \<Rightarrow> 'a ftree"

datatype_new (discs_sels) ('a, 'b, 'c) some_killing =
  SK "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) some_killing + ('a, 'b, 'c) in_here"
and ('a, 'b, 'c) in_here =
  IH1 'b 'a | IH2 'c

datatype_new (discs_sels) 'b nofail1 = NF11 "'b nofail1" 'b | NF12 'b
datatype_new (discs_sels) 'b nofail2 = NF2 "('b nofail2 \<times> 'b \<times> 'b nofail2 \<times> 'b) list"
datatype_new (discs_sels) 'b nofail3 = NF3 'b "('b nofail3 \<times> 'b \<times> 'b nofail3 \<times> 'b) fset"
datatype_new (discs_sels) 'b nofail4 = NF4 "('b nofail4 \<times> ('b nofail4 \<times> 'b \<times> 'b nofail4 \<times> 'b) fset) list"

(*
datatype_new (discs_sels) 'b fail = F "'b fail" 'b "'b fail" "'b list"
datatype_new (discs_sels) 'b fail = F "'b fail" 'b "'b fail" 'b
datatype_new (discs_sels) 'b fail = F1 "'b fail" 'b | F2 "'b fail"
datatype_new (discs_sels) 'b fail = F "'b fail" 'b
*)

datatype_new (discs_sels) l1 = L1 "l2 list"
and l2 = L21 "l1 fset" | L22 l2

datatype_new (discs_sels) kk1 = KK1 kk2
and kk2 = KK2 kk3
and kk3 = KK3 "kk1 list"

datatype_new (discs_sels) t1 = T11 t3 | T12 t2
and t2 = T2 t1
and t3 = T3

datatype_new (discs_sels) t1' = T11' t2' | T12' t3'
and t2' = T2' t1'
and t3' = T3'

(*
datatype_new (discs_sels) fail1 = F1 fail2
and fail2 = F2 fail3
and fail3 = F3 fail1

datatype_new (discs_sels) fail1 = F1 "fail2 list" fail2
and fail2 = F2 "fail2 fset" fail3
and fail3 = F3 fail1

datatype_new (discs_sels) fail1 = F1 "fail2 list" fail2
and fail2 = F2 "fail1 fset" fail1
*)

(* SLOW
datatype_new (discs_sels) ('a, 'c) D1 = A1 "('a, 'c) D2" | B1 "'a list"
and ('a, 'c) D2 = A2 "('a, 'c) D3" | B2 "'c list"
and ('a, 'c) D3 = A3 "('a, 'c) D3" | B3 "('a, 'c) D4" | C3 "('a, 'c) D4" "('a, 'c) D5"
and ('a, 'c) D4 = A4 "('a, 'c) D5" | B4 "'a list list list"
and ('a, 'c) D5 = A5 "('a, 'c) D6"
and ('a, 'c) D6 = A6 "('a, 'c) D7"
and ('a, 'c) D7 = A7 "('a, 'c) D8"
and ('a, 'c) D8 = A8 "('a, 'c) D1 list"
*)

(* fail:
datatype_new (discs_sels) tt1 = TT11 tt2 tt3 | TT12 tt2 tt4
and tt2 = TT2
and tt3 = TT3 tt4
and tt4 = TT4 tt1
*)

datatype_new (discs_sels) k1 = K11 k2 k3 | K12 k2 k4
and k2 = K2
and k3 = K3 k4
and k4 = K4

datatype_new (discs_sels) tt1 = TT11 tt3 tt2 | TT12 tt2 tt4
and tt2 = TT2
and tt3 = TT3 tt1
and tt4 = TT4

(* SLOW
datatype_new (discs_sels) s1 = S11 s2 s3 s4 | S12 s3 | S13 s2 s6 | S14 s4 s2 | S15 s2 s2
and s2 = S21 s7 s5 | S22 s5 s4 s6
and s3 = S31 s1 s7 s2 | S32 s3 s3 | S33 s4 s5
and s4 = S4 s5
and s5 = S5
and s6 = S61 s6 | S62 s1 s2 | S63 s6
and s7 = S71 s8 | S72 s5
and s8 = S8 nat
*)

datatype_new (discs_sels) 'a deadbar = DeadBar "'a \<Rightarrow> 'a"
datatype_new (discs_sels) 'a deadbar_option = DeadBarOption "'a option \<Rightarrow> 'a option"
datatype_new (discs_sels) ('a, 'b) bar = Bar "'b \<Rightarrow> 'a"
datatype_new (discs_sels) ('a, 'b, 'c, 'd) foo = Foo "'d + 'b \<Rightarrow> 'c + 'a"
datatype_new (discs_sels) 'a deadfoo = DeadFoo "'a \<Rightarrow> 'a + 'a"

datatype_new (discs_sels) 'a dead_foo = A
datatype_new (discs_sels) ('a, 'b) use_dead_foo = Y "'a" "'b dead_foo"

datatype_new (discs_sels) d1 = D
datatype_new (discs_sels) d1' = is_D: D

datatype_new (discs_sels) d2 = D nat
datatype_new (discs_sels) d2' = is_D: D nat

datatype_new (discs_sels) d3 = D | E
datatype_new (discs_sels) d3' = D | is_E: E
datatype_new (discs_sels) d3'' = is_D: D | E
datatype_new (discs_sels) d3''' = is_D: D | is_E: E

datatype_new (discs_sels) d4 = D nat | E
datatype_new (discs_sels) d4' = D nat | is_E: E
datatype_new (discs_sels) d4'' = is_D: D nat | E
datatype_new (discs_sels) d4''' = is_D: D nat | is_E: E

datatype_new (discs_sels) d5 = D nat | E int
datatype_new (discs_sels) d5' = D nat | is_E: E int
datatype_new (discs_sels) d5'' = is_D: D nat | E int
datatype_new (discs_sels) d5''' = is_D: D nat | is_E: E int

instance simple :: countable
  by countable_datatype

instance simple'' :: countable
  by countable_datatype

instance mylist :: (countable) countable
  by countable_datatype

instance some_passive :: (countable, countable , countable, countable) countable
  by countable_datatype

(* TODO: Enable once "fset" is registered as countable:

instance hfset :: countable
  by countable_datatype

instance lambda :: countable
  by countable_datatype

instance par_lambda :: (countable) countable
  by countable_datatype
*)

instance I1 and I2 :: (countable) countable
  by countable_datatype

instance tree and forest :: (countable) countable
  by countable_datatype

instance tree' and branch :: (countable) countable
  by countable_datatype

instance bin_rose_tree :: (countable) countable
  by countable_datatype

instance exp and trm and factor :: (countable, countable) countable
  by countable_datatype

instance nofail1 :: (countable) countable
  by countable_datatype

instance nofail2 :: (countable) countable
  by countable_datatype

(* TODO: Enable once "fset" is registered as countable:

instance nofail3 :: (countable) countable
  by countable_datatype

instance nofail4 :: (countable) countable
  by countable_datatype

instance l1 and l2 :: countable
  by countable_datatype
*)

instance kk1 and kk2 :: countable
  by countable_datatype

instance t1 and t2 and t3 :: countable
  by countable_datatype

instance t1' and t2' and t3' :: countable
  by countable_datatype

instance k1 and k2 and k3 and k4 :: countable
  by countable_datatype

instance tt1 and tt2 and tt3 and tt4 :: countable
  by countable_datatype

instance d1 :: countable
  by countable_datatype

instance d1' :: countable
  by countable_datatype

instance d2 :: countable
  by countable_datatype

instance d2' :: countable
  by countable_datatype

instance d3 :: countable
  by countable_datatype

instance d3' :: countable
  by countable_datatype

instance d3'' :: countable
  by countable_datatype

instance d3''' :: countable
  by countable_datatype

instance d4 :: countable
  by countable_datatype

instance d4' :: countable
  by countable_datatype

instance d4'' :: countable
  by countable_datatype

instance d4''' :: countable
  by countable_datatype

instance d5 :: countable
  by countable_datatype

instance d5' :: countable
  by countable_datatype

instance d5'' :: countable
  by countable_datatype

instance d5''' :: countable
  by countable_datatype

datatype_compat simple
datatype_compat simple'
datatype_compat simple''
datatype_compat mylist
datatype_compat some_passive
datatype_compat I1 I2
datatype_compat tree forest
datatype_compat tree' branch
datatype_compat bin_rose_tree
datatype_compat exp trm factor
datatype_compat ftree
datatype_compat nofail1
datatype_compat kk1 kk2 kk3
datatype_compat t1 t2 t3
datatype_compat t1' t2' t3'
datatype_compat k1 k2 k3 k4
datatype_compat tt1 tt2 tt3 tt4
datatype_compat deadbar
datatype_compat deadbar_option
datatype_compat bar
datatype_compat foo
datatype_compat deadfoo
datatype_compat dead_foo
datatype_compat use_dead_foo
datatype_compat d1
datatype_compat d1'
datatype_compat d2
datatype_compat d2'
datatype_compat d3
datatype_compat d3'
datatype_compat d3''
datatype_compat d3'''
datatype_compat d4
datatype_compat d4'
datatype_compat d4''
datatype_compat d4'''
datatype_compat d5
datatype_compat d5'
datatype_compat d5''
datatype_compat d5'''

end
