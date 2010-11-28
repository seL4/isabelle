(*  Title:      HOLCF/HOLCF.thy
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

ML {* path_add "~~/src/HOL/HOLCF/Library" *}

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
(*
lemmas thelubI = lub_eqI
*)

end
