(*  Title:      HOL/Import/Generate-HOL/GenHOL4Base.thy
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

theory GenHOL4Base = HOL4Compat + HOL4Syntax:;

import_segment "hol4";

setup_dump "../HOL" "HOL4Base";

append_dump "theory HOL4Base = HOL4Compat + HOL4Syntax:";

import_theory bool;

const_maps
  T               > True
  F               > False
  "!"             > All
  "/\\"           > "op &"
  "\\/"           > "op |"
  "?"             > Ex
  "?!"            > Ex1
  "~"             > Not
  COND            > If
  bool_case       > Datatype.bool.bool_case
  ONE_ONE         > HOL4Setup.ONE_ONE
  ONTO            > HOL4Setup.ONTO
  TYPE_DEFINITION > HOL4Setup.TYPE_DEFINITION
  LET             > HOL4Compat.LET;

ignore_thms
  BOUNDED_DEF
  BOUNDED_THM
  UNBOUNDED_DEF
  UNBOUNDED_THM;

end_import;

import_theory combin;

const_maps
  o > Fun.comp;

end_import;

import_theory sum;

type_maps
  sum > "+";

const_maps
  INL      > Inl
  INR      > Inr
  ISL      > HOL4Compat.ISL
  ISR      > HOL4Compat.ISR
  OUTL     > HOL4Compat.OUTL
  OUTR     > HOL4Compat.OUTR
  sum_case > Datatype.sum.sum_case;

ignore_thms
  sum_TY_DEF
  sum_ISO_DEF
  IS_SUM_REP
  INL_DEF
  INR_DEF
  sum_axiom
  sum_Axiom;

end_import;

import_theory one;

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

import_theory option;

type_maps
    option > Datatype.option;

const_maps
    NONE        > Datatype.option.None
    SOME        > Datatype.option.Some
    option_case > Datatype.option.option_case
    OPTION_MAP  > Datatype.option_map
    THE         > Datatype.the
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

import_theory marker;
end_import;

import_theory relation;

const_renames
  reflexive > pred_reflexive;

end_import;

import_theory pair;

type_maps
    prod > "*";

const_maps
    ","       > Pair
    FST       > fst
    SND       > snd
    CURRY     > curry
    UNCURRY   > split
    "##"      > prod_fun
    pair_case > split;

ignore_thms
    prod_TY_DEF
    MK_PAIR_DEF
    IS_PAIR_DEF
    ABS_REP_prod
    COMMA_DEF;

end_import;

import_theory num;

type_maps
  num > nat;

const_maps
  SUC > Suc
  0   > 0 :: nat;

ignore_thms
    num_TY_DEF
    num_ISO_DEF
    IS_NUM_REP
    ZERO_REP_DEF
    SUC_REP_DEF
    ZERO_DEF
    SUC_DEF;

end_import;

import_theory prim_rec;

const_maps
    "<" > "op <" :: "[nat,nat]\<Rightarrow>bool";

end_import;

import_theory arithmetic;

const_maps
  ALT_ZERO     > HOL4Compat.ALT_ZERO
  NUMERAL_BIT1 > HOL4Compat.NUMERAL_BIT1
  NUMERAL_BIT2 > HOL4Compat.NUMERAL_BIT2
  NUMERAL      > HOL4Compat.NUMERAL
  num_case     > Nat.nat.nat_case
  ">"          > HOL4Compat.nat_gt
  ">="         > HOL4Compat.nat_ge
  FUNPOW       > HOL4Compat.FUNPOW
  "<="         > "op <="          :: "[nat,nat]\<Rightarrow>bool"
  "+"          > "op +"           :: "[nat,nat]\<Rightarrow>nat"
  "*"          > "op *"           :: "[nat,nat]\<Rightarrow>nat"
  "-"          > "op -"           :: "[nat,nat]\<Rightarrow>nat"
  MIN          > HOL.min          :: "[nat,nat]\<Rightarrow>nat"
  MAX          > HOL.max          :: "[nat,nat]\<Rightarrow>nat"
  DIV          > "Divides.op div" :: "[nat,nat]\<Rightarrow>nat"
  MOD          > "Divides.op mod" :: "[nat,nat]\<Rightarrow>nat"
  EXP          > Nat.power        :: "[nat,nat]\<Rightarrow>nat";

end_import;

import_theory hrat;
end_import;

import_theory hreal;
end_import;

import_theory numeral;
end_import;

import_theory ind_type;
end_import;

import_theory divides;

const_maps
    divides > "Divides.op dvd" :: "[nat,nat]\<Rightarrow>bool";

end_import;

import_theory prime;
end_import;

import_theory list;

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
  MEM       > "List.op mem"
  FILTER    > List.filter
  FOLDL     > List.foldl
  EVERY     > List.list_all
  REVERSE   > List.rev
  LAST      > List.last
  FRONT     > List.butlast
  APPEND    > "List.op @"
  FLAT      > List.concat
  LENGTH    > Nat.size
  REPLICATE > List.replicate
  list_size > HOL4Compat.list_size
  SUM       > HOL4Compat.sum
  FOLDR     > HOL4Compat.FOLDR
  EXISTS    > HOL4Compat.list_exists
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

import_theory pred_set;
end_import;

import_theory operator;
end_import;

import_theory rich_list;
end_import;

import_theory state_transformer;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
