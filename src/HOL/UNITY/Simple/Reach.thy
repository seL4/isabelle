(*  Title:      HOL/UNITY/Reach.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Reachability in Directed Graphs.  From Chandy and Misra, section 6.4.
	[this example took only four days!]
*)

theory Reach = UNITY_Main:

typedecl vertex

types    state = "vertex=>bool"

consts
  init ::  "vertex"

  edges :: "(vertex*vertex) set"

constdefs

  asgt  :: "[vertex,vertex] => (state*state) set"
    "asgt u v == {(s,s'). s' = s(v:= s u | s v)}"

  Rprg :: "state program"
    "Rprg == mk_program ({%v. v=init}, UN (u,v): edges. {asgt u v}, UNIV)"

  reach_invariant :: "state set"
    "reach_invariant == {s. (ALL v. s v --> (init, v) : edges^*) & s init}"

  fixedpoint :: "state set"
    "fixedpoint == {s. ALL (u,v): edges. s u --> s v}"

  metric :: "state => nat"
    "metric s == card {v. ~ s v}"


text{**We assume that the set of vertices is finite*}
axioms 
  finite_graph:  "finite (UNIV :: vertex set)"
  



(*TO SIMPDATA.ML??  FOR CLASET??  *)
lemma ifE [elim!]:
    "[| if P then Q else R;     
        [| P;   Q |] ==> S;     
        [| ~ P; R |] ==> S |] ==> S"
by (simp split: split_if_asm) 


declare Rprg_def [THEN def_prg_Init, simp]

declare asgt_def [THEN def_act_simp,simp]

(*All vertex sets are finite*)
declare finite_subset [OF subset_UNIV finite_graph, iff]

declare reach_invariant_def [THEN def_set_simp, simp]

lemma reach_invariant: "Rprg : Always reach_invariant"
apply (rule AlwaysI, force) 
apply (unfold Rprg_def, constrains) 
apply (blast intro: rtrancl_trans)
done


(*** Fixedpoint ***)

(*If it reaches a fixedpoint, it has found a solution*)
lemma fixedpoint_invariant_correct: 
     "fixedpoint Int reach_invariant = { %v. (init, v) : edges^* }"
apply (unfold fixedpoint_def)
apply (rule equalityI)
apply (auto intro!: ext)
 prefer 2 apply (blast intro: rtrancl_trans)
apply (erule rtrancl_induct, auto)
done

lemma lemma1: 
     "FP Rprg <= fixedpoint"
apply (unfold FP_def fixedpoint_def stable_def constrains_def Rprg_def, auto)
apply (drule bspec, assumption)
apply (simp add: Image_singleton image_iff)
apply (drule fun_cong, auto)
done

lemma lemma2: 
     "fixedpoint <= FP Rprg"
apply (unfold FP_def fixedpoint_def stable_def constrains_def Rprg_def)
apply (auto intro!: ext)
done

lemma FP_fixedpoint: "FP Rprg = fixedpoint"
by (rule equalityI [OF lemma1 lemma2])


(*If we haven't reached a fixedpoint then there is some edge for which u but
  not v holds.  Progress will be proved via an ENSURES assertion that the
  metric will decrease for each suitable edge.  A union over all edges proves
  a LEADSTO assertion that the metric decreases if we are not at a fixedpoint.
  *)

lemma Compl_fixedpoint: "- fixedpoint = (UN (u,v): edges. {s. s u & ~ s v})"
apply (simp add: Compl_FP UN_UN_flatten FP_fixedpoint [symmetric] Rprg_def, auto)
 apply (rule fun_upd_idem, force)
apply (force intro!: rev_bexI simp add: fun_upd_idem_iff)
done

lemma Diff_fixedpoint:
     "A - fixedpoint = (UN (u,v): edges. A Int {s. s u & ~ s v})"
apply (simp add: Diff_eq Compl_fixedpoint, blast)
done


(*** Progress ***)

lemma Suc_metric: "~ s x ==> Suc (metric (s(x:=True))) = metric s"
apply (unfold metric_def)
apply (subgoal_tac "{v. ~ (s (x:=True)) v} = {v. ~ s v} - {x}")
 prefer 2 apply force
apply (simp add: card_Suc_Diff1)
done

lemma metric_less [intro!]: "~ s x ==> metric (s(x:=True)) < metric s"
by (erule Suc_metric [THEN subst], blast)

lemma metric_le: "metric (s(y:=s x | s y)) <= metric s"
apply (case_tac "s x --> s y")
apply (auto intro: less_imp_le simp add: fun_upd_idem)
done

lemma LeadsTo_Diff_fixedpoint:
     "Rprg : ((metric-`{m}) - fixedpoint) LeadsTo (metric-`(lessThan m))"
apply (simp (no_asm) add: Diff_fixedpoint Rprg_def)
apply (rule LeadsTo_UN, auto)
apply (ensures_tac "asgt a b")
 prefer 2 apply blast
apply (simp (no_asm_use) add: not_less_iff_le)
apply (drule metric_le [THEN order_antisym]) 
apply (auto elim: less_not_refl3 [THEN [2] rev_notE])
done

lemma LeadsTo_Un_fixedpoint:
     "Rprg : (metric-`{m}) LeadsTo (metric-`(lessThan m) Un fixedpoint)"
apply (rule LeadsTo_Diff [OF LeadsTo_Diff_fixedpoint [THEN LeadsTo_weaken_R]
                             subset_imp_LeadsTo], auto)
done


(*Execution in any state leads to a fixedpoint (i.e. can terminate)*)
lemma LeadsTo_fixedpoint: "Rprg : UNIV LeadsTo fixedpoint"
apply (rule LessThan_induct, auto)
apply (rule LeadsTo_Un_fixedpoint)
done

lemma LeadsTo_correct: "Rprg : UNIV LeadsTo { %v. (init, v) : edges^* }"
apply (subst fixedpoint_invariant_correct [symmetric])
apply (rule Always_LeadsTo_weaken [OF reach_invariant LeadsTo_fixedpoint], auto)
done

end
