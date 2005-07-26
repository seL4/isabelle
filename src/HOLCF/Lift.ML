
(* legacy ML bindings *)

structure lift =
struct
  val distinct = thms "lift.distinct";
  val inject = thms "lift.inject";
  val exhaust = thm "lift.exhaust";
  val cases = thms "lift.cases";
  val split = thm "lift.split";
  val split_asm = thm "lift.split_asm";
  val induct = thm "lift.induct";
  val recs = thms "lift.recs";
  val simps = thms "lift.simps";
  val size = thms "lift.size";
end;

val cont2cont_flift1 = thm "cont2cont_flift1";
val cont2cont_lift_case = thm "cont2cont_lift_case";
val cont_flift1 = thm "cont_flift1";
val cont_lemmas_ext = thms "cont_lemmas_ext";
val cont_lift_case1 = thm "cont_lift_case1";
val cont_lift_case2 = thm "cont_lift_case2";
val cont_Rep_CFun_app_app = thm "cont_Rep_CFun_app_app";
val cont_Rep_CFun_app = thm "cont_Rep_CFun_app";
val DefE2 = thm "DefE2";
val DefE = thm "DefE";
val Def_inject_less_eq = thm "Def_inject_less_eq";
val Def_inject = thm "Def_inject";
val Def_less_is_eq = thm "Def_less_is_eq";
val Def_not_UU = thm "Def_not_UU";
val flift1_def = thm "flift1_def";
val flift1_Def = thm "flift1_Def";
val flift1_strict = thm "flift1_strict";
val flift2_defined = thm "flift2_defined";
val flift2_def = thm "flift2_def";
val flift2_Def = thm "flift2_Def";
val flift2_strict = thm "flift2_strict";
val inst_lift_pcpo = thm "inst_lift_pcpo";
val less_lift_def = thm "less_lift_def";
val less_lift = thm "less_lift";
val Lift_cases = thm "Lift_cases";
val lift_definedE = thm "lift_definedE";
val lift_distinct1 = thm "lift_distinct1";
val lift_distinct2 = thm "lift_distinct2";
val Lift_exhaust = thm "Lift_exhaust";
val lift_induct = thm "lift_induct";
val liftpair_def = thm "liftpair_def";
val not_Undef_is_Def = thm "not_Undef_is_Def";
