(*  Title:      HOL/Datatype.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(** legacy ML bindings **)

structure bool =
struct
  val distinct = thms "bool.distinct";
  val inject = thms "bool.inject";
  val exhaust = thm "bool.exhaust";
  val cases = thms "bool.cases";
  val split = thm "bool.split";
  val split_asm = thm "bool.split_asm";
  val induct = thm "bool.induct";
  val recs = thms "bool.recs";
  val simps = thms "bool.simps";
  val size = thms "bool.size";
end;

structure sum =
struct
  val distinct = thms "sum.distinct";
  val inject = thms "sum.inject";
  val exhaust = thm "sum.exhaust";
  val cases = thms "sum.cases";
  val split = thm "sum.split";
  val split_asm = thm "sum.split_asm";
  val induct = thm "sum.induct";
  val recs = thms "sum.recs";
  val simps = thms "sum.simps";
  val size = thms "sum.size";
end;

structure unit =
struct
  val distinct = thms "unit.distinct";
  val inject = thms "unit.inject";
  val exhaust = thm "unit.exhaust";
  val cases = thms "unit.cases";
  val split = thm "unit.split";
  val split_asm = thm "unit.split_asm";
  val induct = thm "unit.induct";
  val recs = thms "unit.recs";
  val simps = thms "unit.simps";
  val size = thms "unit.size";
end;

structure prod =
struct
  val distinct = thms "prod.distinct";
  val inject = thms "prod.inject";
  val exhaust = thm "prod.exhaust";
  val cases = thms "prod.cases";
  val split = thm "prod.split";
  val split_asm = thm "prod.split_asm";
  val induct = thm "prod.induct";
  val recs = thms "prod.recs";
  val simps = thms "prod.simps";
  val size = thms "prod.size";
end;

structure option =
struct
  val distinct = thms "option.distinct";
  val inject = thms "option.inject";
  val exhaust = thm "option.exhaust";
  val cases = thms "option.cases";
  val split = thm "option.split";
  val split_asm = thm "option.split_asm";
  val induct = thm "option.induct";
  val recs = thms "option.recs";
  val simps = thms "option.simps";
  val size = thms "option.size";
end;

val elem_o2s = thm "elem_o2s";
val not_None_eq = thm "not_None_eq";
val not_Some_eq = thm "not_Some_eq";
val o2s_empty_eq = thm "o2s_empty_eq";
val option_caseE = thm "option_caseE";
val option_map_None = thm "option_map_None";
val option_map_Some = thm "option_map_Some";
val option_map_def = thm "option_map_def";
val option_map_eq_Some = thm "option_map_eq_Some";
val option_map_o_sum_case = thm "option_map_o_sum_case";
val ospec = thm "ospec";
val sum_case_inject = thm "sum_case_inject";
val sum_case_weak_cong = thm "sum_case_weak_cong";
val surjective_sum = thm "surjective_sum";
