(*  Title:      HOL/Import/Generate-HOLLight/GenHOLLight.thy
    ID:         $Id$
    Author:     Steven Obua (TU Muenchen)
*)

theory GenHOLLight imports "../HOLLightCompat" "../HOL4Syntax" begin;

;skip_import_dir "/home/obua/tmp/cache"

;skip_import on

;import_segment "hollight";

setup_dump "../HOLLight" "HOLLight";

append_dump {*theory HOLLight = "../HOLLightCompat" + "../HOL4Syntax":*};

;import_theory hollight;

ignore_thms
  TYDEF_1
  DEF_one
  TYDEF_prod
  TYDEF_num
  IND_SUC_0_EXISTS
  DEF__0
  DEF_SUC
  DEF_IND_SUC
  DEF_IND_0
  DEF_NUM_REP
  TYDEF_sum
  DEF_INL
  DEF_INR
  TYDEF_option;

type_maps
  ind > Nat.ind
  bool > bool
  fun > fun
  N_1 >  Product_Type.unit
  prod > "*"
  num > nat
  sum > "+"
  option > Datatype.option;

const_renames
  "==" > "eqeq"
  ".." > "dotdot"
  "ALL" > ALL_list;

const_maps
  T > True
  F > False
  ONE_ONE > HOL4Setup.ONE_ONE
  ONTO    > Fun.surj
  "=" > "op ="
  "==>" > "op -->"
  "/\\" > "op &"
  "\\/" > "op |"
  "!" > All
  "?" > Ex
  "?!" > Ex1
  "~" > Not
  o > Fun.comp
  "@" > "Hilbert_Choice.Eps"
  I > Fun.id
  one > Product_Type.Unity
  LET > HOL4Compat.LET
  mk_pair > Product_Type.Pair_Rep
  "," > Pair
  REP_prod > Rep_Prod
  ABS_prod > Abs_Prod
  FST > fst
  SND > snd
  "_0" > 0 :: nat
  SUC > Suc
  PRE > HOLLightCompat.Pred
  NUMERAL > HOL4Compat.NUMERAL
  "+" > HOL.plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
  "*" > HOL.times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "-" > HOL.minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  BIT0 > HOLLightCompat.NUMERAL_BIT0
  BIT1 > HOL4Compat.NUMERAL_BIT1
  INL > Sum_Type.Inl
  INR > Sum_Type.Inr;
 (* HAS_SIZE > HOLLightCompat.HAS_SIZE; *)

(*import_until "TYDEF_sum"

consts
print_theorems

import_until *)

end_import;

append_dump "end";

flush_dump;

import_segment "";

end
