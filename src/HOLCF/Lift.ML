
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

val Def_not_UU = thm "Def_not_UU";
val DefE = thm "DefE";
val DefE2 = thm "DefE2";
val Def_inject_less_eq = thm "Def_inject_less_eq";
val Def_less_is_eq = thm "Def_less_is_eq";
val Lift_cases = thm "Lift_cases";
val Lift_exhaust = thm "Lift_exhaust";
val cont_Rep_CFun_app = thm "cont_Rep_CFun_app";
val cont_Rep_CFun_app_app = thm "cont_Rep_CFun_app_app";
val cont_if = thm "cont_if";
val flift1_Def = thm "flift1_Def";
val flift1_strict = thm "flift1_strict";
val flift1_def = thm "flift1_def";
val flift2_Def = thm "flift2_Def";
val flift2_strict = thm "flift2_strict";
val flift2_def = thm "flift2_def";
val flift2_defined = thm "flift2_defined";
val less_lift = thm "less_lift";
val less_lift_def = thm "less_lift_def";
val liftpair_def = thm "liftpair_def";
val not_Undef_is_Def = thm "not_Undef_is_Def";
