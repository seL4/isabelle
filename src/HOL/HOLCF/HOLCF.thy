(*  Title:      HOL/HOLCF/HOLCF.thy
    Author:     Franz Regensburger

HOLCF -- a semantic extension of HOL by the LCF logic.
*)

theory HOLCF
imports
  Main
  Domain
  Powerdomains
begin

default_sort "domain"

text {* Legacy theorem names deprecated after Isabelle2009-2: *}

lemmas expand_fun_below = fun_below_iff
lemmas below_fun_ext = fun_belowI
lemmas expand_cfun_eq = cfun_eq_iff
lemmas ext_cfun = cfun_eqI
lemmas expand_cfun_below = cfun_below_iff
lemmas below_cfun_ext = cfun_belowI
lemmas monofun_fun_fun = fun_belowD
lemmas monofun_fun_arg = monofunE
lemmas monofun_lub_fun = adm_monofun [THEN admD]
lemmas cont_lub_fun = adm_cont [THEN admD]
lemmas cont2cont_Rep_CFun = cont2cont_APP
lemmas cont_Rep_CFun_app = cont_APP_app
lemmas cont_Rep_CFun_app_app = cont_APP_app_app
lemmas cont_cfun_fun = cont_Rep_cfun1 [THEN contE]
lemmas cont_cfun_arg = cont_Rep_cfun2 [THEN contE]
lemmas contlub_cfun = lub_APP [symmetric]
lemmas contlub_LAM = lub_LAM [symmetric]
lemmas thelubI = lub_eqI
lemmas UU_I = bottomI
lemmas lift_distinct1 = lift.distinct(1)
lemmas lift_distinct2 = lift.distinct(2)
lemmas Def_not_UU = lift.distinct(2)
lemmas Def_inject = lift.inject
lemmas below_UU_iff = below_bottom_iff
lemmas eq_UU_iff = eq_bottom_iff

end
