(*  Title:      HOL/Import/Generate-HOLLight/GenHOLLight.thy
    Author:     Steven Obua, TU Muenchen
    Author:     Cezary Kaliszyk
*)

theory GenHOLLight imports "../HOLLightCompat" "../HOL4Syntax" begin

;import_segment "hollight"

;setup_dump "../HOLLight" "HOLLight";

;append_dump {*theory HOLLight imports "../HOLLightCompat" "../HOL4Syntax" begin *}

import_theory "~~/src/HOL/Import/HOLLight" hollight

;ignore_thms
  (* Unit type *)
  TYDEF_1 DEF_one
  (* Product type *)
  TYDEF_prod "DEF_," DEF_mk_pair REP_ABS_PAIR
  (* Option type *)
  TYDEF_option DEF_NONE DEF_SOME
  (* Sum type *)
  TYDEF_sum DEF_INL DEF_INR DEF_OUTL DEF_OUTR
  (* Naturals *)
  TYDEF_num DEF__0 DEF_SUC
  (* Lists *)
  TYDEF_list DEF_NIL DEF_CONS DEF_HD DEF_TL DEF_MAP2 DEF_ITLIST2 ALL_MAP EX_MAP
  DEF_ASSOC MEM_ASSOC DEF_ZIP EL_TL

  (* list_of_set uses Isabelle lists with HOLLight CARD *)
  DEF_list_of_set LIST_OF_SET_PROPERTIES SET_OF_LIST_OF_SET LENGTH_LIST_OF_SET
  MEM_LIST_OF_SET HAS_SIZE_SET_OF_LIST FINITE_SET_OF_LIST
  (* UNIV *)
  DIMINDEX_FINITE_SUM  DIMINDEX_HAS_SIZE_FINITE_SUM FSTCART_PASTECART
  SNDCART_PASTECART PASTECART_FST_SND PASTECART_EQ FORALL_PASTECART EXISTS_PASTECART
  (* Reals *)
  (* TYDEF_real DEF_real_of_num DEF_real_neg DEF_real_add DEF_real_mul DEF_real_le
  DEF_real_inv REAL_HREAL_LEMMA1 REAL_HREAL_LEMMA2 *)
  (* Integers *)
  (* TYDEF_int DEF_int_divides DEF_int_coprime*)
  (* HOLLight CARD and CASEWISE with Isabelle lists *)
  CARD_SET_OF_LIST_LE CASEWISE CASEWISE_CASES RECURSION_CASEWISE CASEWISE_WORKS
  WF_REC_CASES RECURSION_CASEWISE_PAIRWISE

;type_maps
  bool > HOL.bool
  "fun" > "fun"
  N_1 >  Product_Type.unit
  prod > Product_Type.prod
  ind > Nat.ind
  num > Nat.nat
  sum > Sum_Type.sum
  option > Datatype.option
  list > List.list
(*real > RealDef.real *)
(*int > Int.int *)

;const_renames
  "==" > "eqeq"
  "ALL" > list_ALL
  "EX" > list_EX

;const_maps
  T > HOL.True
  F > HOL.False
  "=" > HOL.eq
  "==>" > HOL.implies
  "/\\" > HOL.conj
  "\\/" > HOL.disj
  "!" > HOL.All
  "?" > HOL.Ex
  "?!" > HOL.Ex1
  "~" > HOL.Not
  COND > HOL.If
  ONE_ONE > Fun.inj
  ONTO > Fun.surj
  o > Fun.comp
  "@" > Hilbert_Choice.Eps
  CHOICE > Hilbert_Choice.Eps
  I > Fun.id
  one > Product_Type.Unity
  LET > HOLLightCompat.LET
  mk_pair > Product_Type.Pair_Rep
  "," > Product_Type.Pair
  FST > Product_Type.fst
  SND > Product_Type.snd
  CURRY > Product_Type.curry
  "_0" > Groups.zero_class.zero :: nat
  SUC > Nat.Suc
  PRE > HOLLightCompat.Pred
  NUMERAL > HOLLightCompat.NUMERAL
  mk_num > Fun.id
  "+" > Groups.plus_class.plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "*" > Groups.times_class.times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "-" > Groups.minus_class.minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "<" > Orderings.ord_class.less :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  "<=" > Orderings.ord_class.less_eq :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  ">" > Orderings.ord_class.greater :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  ">=" > Orderings.ord_class.greater_eq :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  EXP > Power.power_class.power :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  MAX > Orderings.ord_class.max :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  MIN > Orderings.ord_class.min :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  DIV > Divides.div_class.div :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  MOD > Divides.div_class.mod :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  BIT0 > HOLLightCompat.NUMERAL_BIT0
  BIT1 > HOLLightCompat.NUMERAL_BIT1
  INL > Sum_Type.Inl
  INR > Sum_Type.Inr
  OUTL > HOLLightCompat.OUTL
  OUTR > HOLLightCompat.OUTR
  NONE > Datatype.None
  SOME > Datatype.Some
  EVEN > Parity.even_odd_class.even :: "nat \<Rightarrow> bool"
  ODD > HOLLightCompat.ODD
  FACT > Fact.fact_class.fact :: "nat \<Rightarrow> nat"
  WF > Wellfounded.wfP
  NIL > List.list.Nil
  CONS > List.list.Cons
  APPEND > List.append
  REVERSE > List.rev
  LENGTH > List.length
  MAP > List.map
  LAST > List.last
  BUTLAST > List.butlast
  REPLICATE > List.replicate
  ITLIST > List.foldr
  list_ALL > List.list_all
  ALL2 > List.list_all2
  list_EX > List.list_ex
  FILTER > List.filter
  NULL > List.null
  HD > List.hd
  TL > List.tl
  EL > HOLLightList.list_el
  ZIP > List.zip
  MAP2 > HOLLightList.map2
  ITLIST2 > HOLLightList.fold2
  MEM > HOLLightList.list_mem
  set_of_list > List.set
  IN > Set.member
  INSERT > Set.insert
  EMPTY > Orderings.bot_class.bot :: "'a \<Rightarrow> bool"
  GABS > Hilbert_Choice.Eps
  GEQ > HOL.eq
  GSPEC > Set.Collect
  SETSPEC > HOLLightCompat.SETSPEC
  UNION > Lattices.sup_class.sup :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  UNIONS > Complete_Lattices.Sup_class.Sup :: "(('a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  INTER > Lattices.inf_class.inf :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  INTERS > Complete_Lattices.Inf_class.Inf :: "(('a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  DIFF > Groups.minus_class.minus :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  SUBSET > Orderings.ord_class.less_eq :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  PSUBSET > Orderings.ord_class.less :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  DELETE > HOLLightCompat.DELETE
  DISJOINT > HOLLightCompat.DISJOINT
  IMAGE > Set.image
  FINITE > Finite_Set.finite
  INFINITE > HOLLightCompat.INFINITE
  ".." > HOLLightCompat.dotdot
  UNIV > Orderings.top_class.top :: "'a \<Rightarrow> bool"
  MEASURE > HOLLightCompat.MEASURE
(*real_of_num > RealDef.real :: "nat => real"
  real_neg > Groups.uminus_class.uminus :: "real => real"
  real_inv > Fields.inverse_class.inverse :: "real => real"
  real_add > Groups.plus_class.plus :: "real => real => real"
  real_sub > Groups.minus_class.minus :: "real => real => real"
  real_mul > Groups.times_class.times :: "real => real => real"
  real_div > Fields.inverse_class.divide :: "real => real => real"
  real_lt > Orderings.ord_class.less :: "real \<Rightarrow> real \<Rightarrow> bool"
  real_le > Orderings.ord_class.less_eq :: "real \<Rightarrow> real \<Rightarrow> bool"
  real_gt > Orderings.ord_class.greater :: "real \<Rightarrow> real \<Rightarrow> bool"
  real_ge > Orderings.ord_class.greater_eq :: "real \<Rightarrow> real \<Rightarrow> bool"
  real_pow > Power.power_class.power :: "real \<Rightarrow> nat \<Rightarrow> real"
  real_abs > Groups.abs_class.abs :: "real \<Rightarrow> real"
  real_max > Orderings.ord_class.max :: "real \<Rightarrow> real \<Rightarrow> real"
  real_min > Orderings.ord_class.min :: "real \<Rightarrow> real \<Rightarrow> real"
  real_sgn > Groups.sgn_class.sgn :: "real \<Rightarrow> real"*)
(*real_of_int > RealDef.real :: "int => real"
  int_of_real > Archimedean_Field.floor :: "real \<Rightarrow> int"
  dest_int > RealDef.real :: "int => real"
  mk_int > Archimedean_Field.floor :: "real \<Rightarrow> int"
  int_lt > Orderings.ord_class.less :: "int \<Rightarrow> int \<Rightarrow> bool"
  int_le > Orderings.ord_class.less_eq :: "int \<Rightarrow> int \<Rightarrow> bool"
  int_gt > Orderings.ord_class.greater :: "int \<Rightarrow> int \<Rightarrow> bool"
  int_ge > Orderings.ord_class.greater_eq :: "int \<Rightarrow> int \<Rightarrow> bool"
  int_of_num > Nat.semiring_1_class.of_nat :: "nat \<Rightarrow> int"
  int_neg > Groups.uminus_class.uminus :: "int \<Rightarrow> int"
  int_add > Groups.plus_class.plus :: "int => int => int"
  int_sub > Groups.minus_class.minus :: "int => int => int"
  int_mul > Groups.times_class.times :: "int => int => int"
  int_abs > Groups.abs_class.abs :: "int \<Rightarrow> int"
  int_max > Orderings.ord_class.max :: "int \<Rightarrow> int \<Rightarrow> int"
  int_min > Orderings.ord_class.min :: "int \<Rightarrow> int \<Rightarrow> int"
  int_sgn > Groups.sgn_class.sgn :: "int \<Rightarrow> int"
  int_pow > Power.power_class.power :: "int \<Rightarrow> nat \<Rightarrow> int"
  int_div > HOLLightInt.hl_div :: "int \<Rightarrow> int \<Rightarrow> int"
  div > HOLLightInt.hl_div :: "int \<Rightarrow> int \<Rightarrow> int"
  mod_int > HOLLightInt.hl_mod :: "int \<Rightarrow> int \<Rightarrow> int"
  rem > HOLLightInt.hl_mod :: "int \<Rightarrow> int \<Rightarrow> int"
  int_divides > Rings.dvd_class.dvd :: "int \<Rightarrow> int \<Rightarrow> bool"
  int_mod > HOLLightInt.int_mod :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  int_gcd > HOLLightInt.int_gcd :: "int \<times> int \<Rightarrow> int"
  int_coprime > HOLLightInt.int_coprime :: "int \<times> int \<Rightarrow> bool"
  eqeq > HOLLightInt.eqeq*)

;end_import

;append_dump "end"

;flush_dump

;import_segment ""

end
