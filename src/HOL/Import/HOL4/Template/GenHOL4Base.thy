(*  Title:      HOL/Import/Generate-HOL/GenHOL4Base.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Base
imports "../../HOL4Syntax" "../Compatibility"
begin

import_segment "hol4"

setup_dump "../Generated" "HOL4Base"

append_dump {*theory HOL4Base
imports "../../HOL4Syntax" "../Compatibility"
begin
*}

import_theory "~~/src/HOL/Import/HOL4/Generated" bool;

type_maps
  bool            > HOL.bool;

const_maps
  T               > HOL.True
  F               > HOL.False
  "!"             > HOL.All
  "/\\"           > HOL.conj
  "\\/"           > HOL.disj
  "?"             > HOL.Ex
  "?!"            > HOL.Ex1
  "~"             > HOL.Not
  COND            > HOL.If
  bool_case       > Product_Type.bool.bool_case
  ONE_ONE         > HOL4Setup.ONE_ONE
  ONTO            > Fun.surj
  TYPE_DEFINITION > HOL4Setup.TYPE_DEFINITION
  LET             > Compatibility.LET;

ignore_thms
  BOUNDED_DEF
  BOUNDED_THM
  UNBOUNDED_DEF
  UNBOUNDED_THM;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" combin;

const_maps
  o > Fun.comp;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" sum;

type_maps
  sum > Sum_Type.sum;

const_maps
  INL      > Sum_Type.Inl
  INR      > Sum_Type.Inr
  ISL      > Compatibility.ISL
  ISR      > Compatibility.ISR
  OUTL     > Compatibility.OUTL
  OUTR     > Compatibility.OUTR
  sum_case > Sum_Type.sum.sum_case;

ignore_thms
  sum_TY_DEF
  sum_ISO_DEF
  IS_SUM_REP
  INL_DEF
  INR_DEF
  sum_Axiom;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" one;

type_maps
  one > Product_Type.unit;

const_maps
  one > Product_Type.Unity;

ignore_thms
    one_TY_DEF
    one_axiom
    one_Axiom
    one_DEF;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" option;

type_maps
    option > Option.option;

const_maps
    NONE        > Option.option.None
    SOME        > Option.option.Some
    option_case > Option.option.option_case
    OPTION_MAP  > Option.map
    THE         > Option.the
    IS_SOME     > Compatibility.IS_SOME
    IS_NONE     > Compatibility.IS_NONE
    OPTION_JOIN > Compatibility.OPTION_JOIN;

ignore_thms
    option_axiom
    option_Axiom
    option_TY_DEF
    option_REP_ABS_DEF
    SOME_DEF
    NONE_DEF;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" marker;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" relation;

const_renames
  reflexive > pred_reflexive;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" pair;

type_maps
    prod > Product_Type.prod;

const_maps
    ","       > Product_Type.Pair
    FST       > Product_Type.fst
    SND       > Product_Type.snd
    CURRY     > Product_Type.curry
    UNCURRY   > Product_Type.prod.prod_case
    "##"      > Product_Type.map_pair
    pair_case > Product_Type.prod.prod_case;

ignore_thms
    prod_TY_DEF
    MK_PAIR_DEF
    IS_PAIR_DEF
    ABS_REP_prod
    COMMA_DEF;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" num;

type_maps
  num > Nat.nat;

const_maps
  SUC > Nat.Suc
  0   > Groups.zero_class.zero :: nat;

ignore_thms
    num_TY_DEF
    num_ISO_DEF
    IS_NUM_REP
    ZERO_REP_DEF
    SUC_REP_DEF
    ZERO_DEF
    SUC_DEF;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prim_rec;

const_maps
    "<" > Orderings.ord_class.less :: "nat \<Rightarrow> nat \<Rightarrow> bool";

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" arithmetic;

const_maps
  ALT_ZERO     > Compatibility.ALT_ZERO
  NUMERAL_BIT1 > Compatibility.NUMERAL_BIT1
  NUMERAL_BIT2 > Compatibility.NUMERAL_BIT2
  NUMERAL      > Compatibility.NUMERAL
  num_case     > Nat.nat.nat_case
  ">"          > Compatibility.nat_gt
  ">="         > Compatibility.nat_ge
  FUNPOW       > Compatibility.FUNPOW
  "<="         > Orderings.ord_class.less_eq :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  "+"          > Groups.plus_class.plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "*"          > Groups.times_class.times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "-"          > Groups.minus_class.minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  MIN          > Orderings.ord_class.min :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  MAX          > Orderings.ord_class.max :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  DIV          > Divides.div_class.div :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  MOD          > Divides.div_class.mod :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  EXP          > Power.power_class.power :: "nat \<Rightarrow> nat \<Rightarrow> nat";

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" hrat;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" hreal;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" numeral;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" ind_type;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" divides;

const_maps
  divides > Rings.dvd_class.dvd :: "nat \<Rightarrow> nat \<Rightarrow> bool";

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" prime;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" list;

type_maps
    list > List.list;

const_maps
  CONS      > List.list.Cons
  NIL       > List.list.Nil
  list_case > List.list.list_case
  NULL      > List.null
  HD        > List.hd
  TL        > List.tl
  MAP       > List.map
  MEM       > Compatibility.list_mem
  FILTER    > List.filter
  FOLDL     > List.foldl
  EVERY     > List.list_all
  REVERSE   > List.rev
  LAST      > List.last
  FRONT     > List.butlast
  APPEND    > List.append
  FLAT      > List.concat
  LENGTH    > Nat.size_class.size
  REPLICATE > List.replicate
  list_size > Compatibility.list_size
  SUM       > Compatibility.sum
  FOLDR     > Compatibility.FOLDR
  EXISTS    > List.list_ex
  MAP2      > Compatibility.map2
  ZIP       > Compatibility.ZIP
  UNZIP     > Compatibility.unzip;

ignore_thms
  list_TY_DEF
  list_repfns
  list0_def
  list1_def
  NIL
  CONS_def;

end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" pred_set;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" operator;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" rich_list;
end_import;

import_theory "~~/src/HOL/Import/HOL4/Generated" state_transformer;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
