(* $Id$ *)

theory Dagstuhl
imports Stream
begin

consts
  y  :: "'a"

definition
  YS :: "'a stream"
  "YS = fix$(LAM x. y && x)"
  YYS :: "'a stream"
  "YYS = fix$(LAM z. y && y && z)"

lemma YS_def2: "YS = y && YS"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (rule YS_def [THEN eq_reflection])
  apply (rule beta_cfun)
  apply simp
  done

lemma YYS_def2: "YYS = y && y && YYS"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (rule YYS_def [THEN eq_reflection])
  apply (rule beta_cfun)
  apply simp
  done


lemma lemma3: "YYS << y && YYS"
  apply (rule YYS_def [THEN eq_reflection, THEN def_fix_ind])
  apply simp_all
  apply (rule monofun_cfun_arg)
  apply (rule monofun_cfun_arg)
  apply assumption
  done

lemma lemma4: "y && YYS << YYS"
  apply (subst YYS_def2)
  back
  apply (rule monofun_cfun_arg)
  apply (rule lemma3)
  done

lemma lemma5: "y && YYS = YYS"
  apply (rule antisym_less)
  apply (rule lemma4)
  apply (rule lemma3)
  done

lemma wir_moel: "YS = YYS"
  apply (rule stream.take_lemmas)
  apply (induct_tac n)
  apply (simp (no_asm) add: stream.rews)
  apply (subst YS_def2)
  apply (subst YYS_def2)
  apply (simp add: stream.rews)
  apply (rule lemma5 [symmetric, THEN subst])
  apply (rule refl)
  done

(* ------------------------------------------------------------------------ *)
(* Zweite L"osung: Bernhard Möller                                          *)
(* statt Beweis von  wir_moel "uber take_lemma beidseitige Inclusion        *)
(* verwendet lemma5                                                         *)
(* ------------------------------------------------------------------------ *)

lemma lemma6: "YYS << YS"
  apply (unfold YYS_def)
  apply (rule fix_least)
  apply (subst beta_cfun)
  apply (tactic "cont_tacR 1")
  apply (simp add: YS_def2 [symmetric])
  done

lemma lemma7: "YS << YYS"
  apply (rule YS_def [THEN eq_reflection, THEN def_fix_ind])
  apply simp_all
  apply (subst lemma5 [symmetric])
  apply (erule monofun_cfun_arg)
  done

lemma wir_moel': "YS = YYS"
  apply (rule antisym_less)
  apply (rule lemma7)
  apply (rule lemma6)
  done

end
