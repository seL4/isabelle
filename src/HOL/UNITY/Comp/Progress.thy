(*  Title:      HOL/UNITY/Transformers
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

David Meier's thesis
*)

header{*Progress Set Examples*}

theory Progress = UNITY_Main:

subsection {*The Composition of Two Single-Assignment Programs*}
text{*Thesis Section 4.4.2*}

constdefs
  FF :: "int program"
    "FF == mk_total_program (UNIV, {range (\<lambda>x. (x, x+1))}, UNIV)"

  GG :: "int program"
    "GG == mk_total_program (UNIV, {range (\<lambda>x. (x, 2*x))}, UNIV)"

subsubsection {*Calculating @{term "wens_set FF (atLeast k)"}*}

lemma Domain_actFF: "Domain (range (\<lambda>x::int. (x, x + 1))) = UNIV"
by force

lemma FF_eq:
      "FF = mk_program (UNIV, {range (\<lambda>x. (x, x+1))}, UNIV)"
by (simp add: FF_def mk_total_program_def totalize_def totalize_act_def
              program_equalityI Domain_actFF)

lemma wp_actFF:
     "wp (range (\<lambda>x::int. (x, x + 1))) (atLeast k) = atLeast (k - 1)"
by (force simp add: wp_def)

lemma wens_FF: "wens FF (range (\<lambda>x. (x, x+1))) (atLeast k) = atLeast (k - 1)"
by (force simp add: FF_eq wens_single_eq wp_actFF)

lemma single_valued_actFF: "single_valued (range (\<lambda>x::int. (x, x + 1)))"
by (force simp add: single_valued_def)

lemma wens_single_finite_FF:
     "wens_single_finite (range (\<lambda>x. (x, x+1))) (atLeast k) n =
      atLeast (k - int n)"
apply (induct n, simp)
apply (force simp add: wens_FF
            def_wens_single_finite_Suc_eq_wens [OF FF_eq single_valued_actFF])
done

lemma wens_single_FF_eq_UNIV:
     "wens_single (range (\<lambda>x::int. (x, x + 1))) (atLeast k) = UNIV"
apply (auto simp add: wens_single_eq_Union)
apply (rule_tac x="nat (k-x)" in exI)
apply (simp add: wens_single_finite_FF)
done

lemma wens_set_FF:
     "wens_set FF (atLeast k) = insert UNIV (atLeast ` atMost k)"
apply (auto simp add: wens_set_single_eq [OF FF_eq single_valued_actFF]
                      wens_single_FF_eq_UNIV wens_single_finite_FF)
apply (erule notE)
apply (rule_tac x="nat (k-xa)" in range_eqI)
apply (simp add: wens_single_finite_FF)
done

subsubsection {*Proving @{term "FF \<in> UNIV leadsTo atLeast (k::int)"}*}

lemma atLeast_ensures: "FF \<in> atLeast (k - 1) ensures atLeast (k::int)"
apply (simp add: Progress.wens_FF [symmetric] wens_ensures)
apply (simp add: wens_ensures FF_eq)
done

lemma atLeast_leadsTo: "FF \<in> atLeast (k - int n) leadsTo atLeast (k::int)"
apply (induct n)
 apply (simp_all add: leadsTo_refl)
apply (rule_tac A = "atLeast (k - int n - 1)" in leadsTo_weaken_L)
 apply (blast intro: leadsTo_Trans atLeast_ensures, force) 
done

lemma UN_atLeast_UNIV: "(\<Union>n. atLeast (k - int n)) = UNIV"
apply auto 
apply (rule_tac x = "nat (k - x)" in exI, simp) 
done

lemma FF_leadsTo: "FF \<in> UNIV leadsTo atLeast (k::int)"
apply (subst UN_atLeast_UNIV [symmetric]) 
apply (rule leadsTo_UN [OF atLeast_leadsTo]) 
done

text{*Result (4.39): Applying the Union Theorem*}
theorem "FF\<squnion>GG \<in> atLeast 0 leadsTo atLeast (k::int)"
apply (subgoal_tac "FF\<squnion>GG \<in> (atLeast 0 \<inter> atLeast 0) leadsTo atLeast k")
 apply simp
apply (rule_tac T = "atLeast 0" in leadsTo_Union)
  apply (simp add: awp_iff FF_def, constrains)
 apply (simp add: awp_iff GG_def wens_set_FF, constrains)
apply (rule leadsTo_weaken_L [OF FF_leadsTo], simp) 
done

end
