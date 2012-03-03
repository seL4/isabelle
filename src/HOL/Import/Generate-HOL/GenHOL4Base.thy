(*  Title:      HOL/Import/Generate-HOL/GenHOL4Base.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Base imports "../HOL4Compat" "../HOL4Syntax" begin;

import_segment "hol4";

setup_dump "../HOL" "HOL4Base";

append_dump {*theory HOL4Base imports "../HOL4Compat" "../HOL4Syntax" begin*};

import_theory "~~/src/HOL/Import/HOL" bool;

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
  LET             > HOL4Compat.LET;

ignore_thms
  BOUNDED_DEF
  BOUNDED_THM
  UNBOUNDED_DEF
  UNBOUNDED_THM;

end_import;

import_theory "~~/src/HOL/Import/HOL" combin;

const_maps
  o > Fun.comp;

end_import;

import_theory "~~/src/HOL/Import/HOL" sum;

type_maps
  sum > Sum_Type.sum;

const_maps
  INL      > Sum_Type.Inl
  INR      > Sum_Type.Inr
  ISL      > HOL4Compat.ISL
  ISR      > HOL4Compat.ISR
  OUTL     > HOL4Compat.OUTL
  OUTR     > HOL4Compat.OUTR
  sum_case > Sum_Type.sum.sum_case;

ignore_thms
  sum_TY_DEF
  sum_ISO_DEF
  IS_SUM_REP
  INL_DEF
  INR_DEF
  sum_Axiom;

end_import;

import_theory "~~/src/HOL/Import/HOL" one;

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

import_theory "~~/src/HOL/Import/HOL" option;

type_maps
    option > Option.option;

const_maps
    NONE        > Option.option.None
    SOME        > Option.option.Some
    option_case > Option.option.option_case
    OPTION_MAP  > Option.map
    THE         > Option.the
    IS_SOME     > HOL4Compat.IS_SOME
    IS_NONE     > HOL4Compat.IS_NONE
    OPTION_JOIN > HOL4Compat.OPTION_JOIN;

ignore_thms
    option_axiom
    option_Axiom
    option_TY_DEF
    option_REP_ABS_DEF
    SOME_DEF
    NONE_DEF;

end_import;

import_theory "~~/src/HOL/Import/HOL" marker;
end_import;

import_theory "~~/src/HOL/Import/HOL" relation;

const_renames
  reflexive > pred_reflexive;

end_import;

import_theory "~~/src/HOL/Import/HOL" pair;

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

import_theory "~~/src/HOL/Import/HOL" num;

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

import_theory "~~/src/HOL/Import/HOL" prim_rec;

const_maps
    "<" > Orderings.ord_class.less :: "nat \<Rightarrow> nat \<Rightarrow> bool";

end_import;

import_theory "~~/src/HOL/Import/HOL" arithmetic;

const_maps
  ALT_ZERO     > HOL4Compat.ALT_ZERO
  NUMERAL_BIT1 > HOL4Compat.NUMERAL_BIT1
  NUMERAL_BIT2 > HOL4Compat.NUMERAL_BIT2
  NUMERAL      > HOL4Compat.NUMERAL
  num_case     > Nat.nat.nat_case
  ">"          > HOL4Compat.nat_gt
  ">="         > HOL4Compat.nat_ge
  FUNPOW       > HOL4Compat.FUNPOW
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

import_theory "~~/src/HOL/Import/HOL" hrat;
end_import;

import_theory "~~/src/HOL/Import/HOL" hreal;
end_import;

import_theory "~~/src/HOL/Import/HOL" numeral;
end_import;

import_theory "~~/src/HOL/Import/HOL" ind_type;
end_import;

import_theory "~~/src/HOL/Import/HOL" divides;

const_maps
  divides > Rings.dvd_class.dvd :: "nat \<Rightarrow> nat \<Rightarrow> bool";

end_import;

import_theory "~~/src/HOL/Import/HOL" prime;
end_import;

import_theory "~~/src/HOL/Import/HOL" list;

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
  MEM       > HOL4Compat.list_mem
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
  list_size > HOL4Compat.list_size
  SUM       > HOL4Compat.sum
  FOLDR     > HOL4Compat.FOLDR
  EXISTS    > List.list_ex
  MAP2      > HOL4Compat.map2
  ZIP       > HOL4Compat.ZIP
  UNZIP     > HOL4Compat.unzip;

ignore_thms
  list_TY_DEF
  list_repfns
  list0_def
  list1_def
  NIL
  CONS_def;

end_import;

import_theory "~~/src/HOL/Import/HOL" pred_set;
end_import;

import_theory "~~/src/HOL/Import/HOL" operator;
end_import;

import_theory "~~/src/HOL/Import/HOL" rich_list;
end_import;

import_theory "~~/src/HOL/Import/HOL" state_transformer;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
