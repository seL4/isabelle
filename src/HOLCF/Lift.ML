
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
val UU_lift_def = thm "UU_lift_def";
val Undef_eq_UU = thm "Undef_eq_UU";
val chain_mono2_po = thm "chain_mono2_po";
val cont2cont_CF1L_rev2 = thm "cont2cont_CF1L_rev2";
val cont_Rep_CFun_app = thm "cont_Rep_CFun_app";
val cont_Rep_CFun_app_app = thm "cont_Rep_CFun_app_app";
val cont_flift1_arg = thm "cont_flift1_arg";
val cont_flift1_arg_and_not_arg = thm "cont_flift1_arg_and_not_arg";
val cont_flift1_not_arg = thm "cont_flift1_not_arg";
val cont_flift2_arg = thm "cont_flift2_arg";
val cont_if = thm "cont_if";
val cpo_lift = thm "cpo_lift";
val flat_imp_chfin_poo = thm "flat_imp_chfin_poo";
val flift1_Def = thm "flift1_Def";
val flift1_UU = thm "flift1_UU";
val flift1_def = thm "flift1_def";
val flift2_Def = thm "flift2_Def";
val flift2_UU = thm "flift2_UU";
val flift2_def = thm "flift2_def";
val flift2_nUU = thm "flift2_nUU";
val inst_lift_pcpo = thm "inst_lift_pcpo";
val inst_lift_po = thm "inst_lift_po";
val least_lift = thm "least_lift";
val less_lift = thm "less_lift";
val less_lift_def = thm "less_lift_def";
val liftpair_def = thm "liftpair_def";
val minimal_lift = thm "minimal_lift";
val notUndef_I = thm "notUndef_I";
val not_Undef_is_Def = thm "not_Undef_is_Def";
