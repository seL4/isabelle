(*  Title:      HOLCF/HOLCF.thy
    Author:     Franz Regensburger

HOLCF -- a semantic extension of HOL by the LCF logic.
*)

theory HOLCF
imports
  Domain ConvexPD Algebraic Universal Sum_Cpo Main
uses
  "holcf_logic.ML"
  "Tools/adm_tac.ML"
begin

defaultsort pcpo

declaration {* fn _ =>
  Simplifier.map_ss (fn simpset => simpset addSolver
    (mk_solver' "adm_tac" (fn ss =>
      Adm.adm_tac (Simplifier.the_context ss)
        (cut_facts_tac (Simplifier.prems_of_ss ss) THEN' cont_tacRs ss))));
*}

text {* Legacy theorem names *}

lemmas sq_ord_less_eq_trans = below_eq_trans
lemmas sq_ord_eq_less_trans = eq_below_trans
lemmas refl_less = below_refl
lemmas trans_less = below_trans
lemmas antisym_less = below_antisym
lemmas antisym_less_inverse = below_antisym_inverse
lemmas box_less = box_below
lemmas rev_trans_less = rev_below_trans
lemmas not_less2not_eq = not_below2not_eq
lemmas less_UU_iff = below_UU_iff
lemmas flat_less_iff = flat_below_iff
lemmas adm_less = adm_below
lemmas adm_not_less = adm_not_below
lemmas adm_compact_not_less = adm_compact_not_below
lemmas less_fun_def = below_fun_def
lemmas expand_fun_less = expand_fun_below
lemmas less_fun_ext = below_fun_ext
lemmas less_discr_def = below_discr_def
lemmas discr_less_eq = discr_below_eq
lemmas less_unit_def = below_unit_def
lemmas less_cprod_def = below_prod_def
lemmas prod_lessI = prod_belowI
lemmas Pair_less_iff = Pair_below_iff
lemmas fst_less_iff = fst_below_iff
lemmas snd_less_iff = snd_below_iff
lemmas expand_cfun_less = expand_cfun_below
lemmas less_cfun_ext = below_cfun_ext
lemmas injection_less = injection_below
lemmas approx_less = approx_below
lemmas profinite_less_ext = profinite_below_ext
lemmas less_up_def = below_up_def
lemmas not_Iup_less = not_Iup_below
lemmas Iup_less = Iup_below
lemmas up_less = up_below
lemmas cpair_less = cpair_below
lemmas less_cprod = below_cprod
lemmas cfst_less_iff = cfst_below_iff
lemmas csnd_less_iff = csnd_below_iff
lemmas Def_inject_less_eq = Def_below_Def
lemmas Def_less_is_eq = Def_below_iff
lemmas spair_less_iff = spair_below_iff
lemmas less_sprod = below_sprod
lemmas spair_less = spair_below
lemmas sfst_less_iff = sfst_below_iff
lemmas ssnd_less_iff = ssnd_below_iff
lemmas fix_least_less = fix_least_below
lemmas dist_less_one = dist_below_one
lemmas less_ONE = below_ONE
lemmas ONE_less_iff = ONE_below_iff
lemmas less_sinlD = below_sinlD
lemmas less_sinrD = below_sinrD

end
