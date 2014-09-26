(*  Title:      HOL/Datatype_Examples/Misc_Codatatype.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Miscellaneous codatatype definitions.
*)

header {* Miscellaneous Codatatype Definitions *}

theory Misc_Codatatype
imports "~~/src/HOL/Library/FSet"
begin

codatatype simple = X1 | X2 | X3 | X4

codatatype simple' = X1' unit | X2' unit | X3' unit | X4' unit

codatatype simple'' = X1'' nat int | X2''

codatatype 'a stream = Stream (shd: 'a) (stl: "'a stream")

codatatype 'a mylist = MyNil | MyCons (myhd: 'a) (mytl: "'a mylist")

codatatype ('b, 'c :: ord, 'd, 'e) some_passive =
  SP1 "('b, 'c, 'd, 'e) some_passive" | SP2 'b | SP3 'c | SP4 'd | SP5 'e

codatatype 'a multi_live_direct1 = MultiLiveDirect1 'a
codatatype 'a multi_live_direct2 = MultiLiveDirect2 'a 'a
codatatype 'a multi_live_direct3 = MultiLiveDirect3 'a 'a 'a
codatatype 'a multi_live_direct4 = MultiLiveDirect4 'a 'a 'a 'a
codatatype 'a multi_live_direct5 = MultiLiveDirect5 'a 'a 'a 'a 'a
codatatype 'a multi_live_direct6 = MultiLiveDirect6 'a 'a 'a 'a 'a 'a
codatatype 'a multi_live_direct7 = MultiLiveDirect7 'a 'a 'a 'a 'a 'a 'a
codatatype 'a multi_live_direct8 = MultiLiveDirect8 'a 'a 'a 'a 'a 'a 'a 'a
codatatype 'a multi_live_direct9 = MultiLiveDirect9 'a 'a 'a 'a 'a 'a 'a 'a 'a

datatype 'a live_and_fun = LiveAndFun nat "nat \<Rightarrow> 'a"

codatatype lambda =
  Var string |
  App lambda lambda |
  Abs string lambda |
  Let "(string \<times> lambda) fset" lambda

codatatype 'a par_lambda =
  PVar 'a |
  PApp "'a par_lambda" "'a par_lambda" |
  PAbs 'a "'a par_lambda" |
  PLet "('a \<times> 'a par_lambda) fset" "'a par_lambda"

(*
  ('a, 'b1, 'b2) F1 = 'a * 'b1 + 'a * 'b2
  ('a, 'b1, 'b2) F2 = unit + 'b1 * 'b2
*)

codatatype 'a p = P "'a + 'a p"

codatatype 'a J1 = J11 'a "'a J1" | J12 'a "'a J2"
and 'a J2 = J21 | J22 "'a J1" "'a J2"

codatatype 'a tree = TEmpty | TNode 'a "'a forest"
and 'a forest = FNil | FCons "'a tree" "'a forest"

codatatype 'a tree' = TEmpty' | TNode' "'a branch" "'a branch"
and 'a branch = Branch 'a "'a tree'"

codatatype 'a bin_rose_tree = BRTree 'a "'a bin_rose_tree mylist" "'a bin_rose_tree mylist"

codatatype ('a, 'b) exp = Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) exp"
and ('a, 'b) trm = Factor "('a, 'b) factor" | Prod "('a, 'b) factor" "('a, 'b) trm"
and ('a, 'b) factor = C 'a | V 'b | Paren "('a, 'b) exp"

codatatype ('a, 'b, 'c) some_killing =
  SK "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) some_killing + ('a, 'b, 'c) in_here"
and ('a, 'b, 'c) in_here =
  IH1 'b 'a | IH2 'c

codatatype ('a, 'b, 'c) some_killing' =
  SK' "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) some_killing' + ('a, 'b, 'c) in_here'"
and ('a, 'b, 'c) in_here' =
  IH1' 'b | IH2' 'c

codatatype ('a, 'b, 'c) some_killing'' =
  SK'' "'a \<Rightarrow> ('a, 'b, 'c) in_here''"
and ('a, 'b, 'c) in_here'' =
  IH1'' 'b 'a | IH2'' 'c

codatatype ('b, 'c) less_killing = LK "'b \<Rightarrow> 'c"

codatatype 'b poly_unit = U "'b \<Rightarrow> 'b poly_unit"
codatatype 'b cps = CPS1 'b | CPS2 "'b \<Rightarrow> 'b cps"

codatatype ('b1, 'b2, 'b3, 'b4, 'b5, 'b6, 'b7, 'b8, 'b9) fun_rhs =
  FR "'b1 \<Rightarrow> 'b2 \<Rightarrow> 'b3 \<Rightarrow> 'b4 \<Rightarrow> 'b5 \<Rightarrow> 'b6 \<Rightarrow> 'b7 \<Rightarrow> 'b8 \<Rightarrow> 'b9 \<Rightarrow>
      ('b1, 'b2, 'b3, 'b4, 'b5, 'b6, 'b7, 'b8, 'b9) fun_rhs"

codatatype ('b1, 'b2, 'b3, 'b4, 'b5, 'b6, 'b7, 'b8, 'b9, 'b10, 'b11, 'b12, 'b13, 'b14, 'b15, 'b16, 'b17,
        'b18, 'b19, 'b20) fun_rhs' =
  FR' "'b1 \<Rightarrow> 'b2 \<Rightarrow> 'b3 \<Rightarrow> 'b4 \<Rightarrow> 'b5 \<Rightarrow> 'b6 \<Rightarrow> 'b7 \<Rightarrow> 'b8 \<Rightarrow> 'b9 \<Rightarrow> 'b10 \<Rightarrow> 'b11 \<Rightarrow> 'b12 \<Rightarrow> 'b13 \<Rightarrow> 'b14 \<Rightarrow>
       'b15 \<Rightarrow> 'b16 \<Rightarrow> 'b17 \<Rightarrow> 'b18 \<Rightarrow> 'b19 \<Rightarrow> 'b20 \<Rightarrow>
       ('b1, 'b2, 'b3, 'b4, 'b5, 'b6, 'b7, 'b8, 'b9, 'b10, 'b11, 'b12, 'b13, 'b14, 'b15, 'b16, 'b17,
        'b18, 'b19, 'b20) fun_rhs'"

codatatype ('a, 'b, 'c) wit3_F1 = W1 'a "('a, 'b, 'c) wit3_F1" "('a, 'b, 'c) wit3_F2"
and ('a, 'b, 'c) wit3_F2 = W2 'b "('a, 'b, 'c) wit3_F2"
and ('a, 'b, 'c) wit3_F3 = W31 'a 'b "('a, 'b, 'c) wit3_F1" | W32 'c 'a 'b "('a, 'b, 'c) wit3_F1"

codatatype ('c, 'e, 'g) coind_wit1 =
       CW1 'c "('c, 'e, 'g) coind_wit1" "('c, 'e, 'g) ind_wit" "('c, 'e, 'g) coind_wit2"
and ('c, 'e, 'g) coind_wit2 =
       CW21 "('c, 'e, 'g) coind_wit2" 'e | CW22 'c 'g
and ('c, 'e, 'g) ind_wit =
       IW1 | IW2 'c

codatatype ('b, 'a) bar = BAR "'a \<Rightarrow> 'b"
codatatype ('a, 'b, 'c, 'd) foo = FOO "'d + 'b \<Rightarrow> 'c + 'a"

codatatype (dead 'a) dead_foo = A
codatatype ('a, 'b) use_dead_foo = Y 'a "'b dead_foo"

codatatype 'a phantom = A
codatatype 'a use_phantom = Y 'a "'a use_phantom phantom"

(* SLOW, MEMORY-HUNGRY
codatatype ('a, 'c) D1 = A1 "('a, 'c) D2" | B1 "'a list"
and ('a, 'c) D2 = A2 "('a, 'c) D3" | B2 "'c list"
and ('a, 'c) D3 = A3 "('a, 'c) D3" | B3 "('a, 'c) D4" | C3 "('a, 'c) D4" "('a, 'c) D5"
and ('a, 'c) D4 = A4 "('a, 'c) D5" | B4 "'a list list list"
and ('a, 'c) D5 = A5 "('a, 'c) D6"
and ('a, 'c) D6 = A6 "('a, 'c) D7"
and ('a, 'c) D7 = A7 "('a, 'c) D8"
and ('a, 'c) D8 = A8 "('a, 'c) D1 list"
*)

end
