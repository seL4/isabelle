(*  Title:      HOL/UNITY/Comp/Handshake.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Handshake Protocol

From Misra, "Asynchronous Compositions of Programs", Section 5.3.2
*)

theory Handshake imports "../UNITY_Main" begin

record state =
  BB :: bool
  NF :: nat
  NG :: nat

definition
  (*F's program*)
  cmdF :: "(state*state) set"
  where "cmdF = {(s,s'). s' = s (|NF:= Suc(NF s), BB:=False|) & BB s}"

definition
  F :: "state program"
  where "F = mk_total_program ({s. NF s = 0 & BB s}, {cmdF}, UNIV)"

definition
  (*G's program*)
  cmdG :: "(state*state) set"
  where "cmdG = {(s,s'). s' = s (|NG:= Suc(NG s), BB:=True|) & ~ BB s}"

definition
  G :: "state program"
  where "G = mk_total_program ({s. NG s = 0 & BB s}, {cmdG}, UNIV)"

definition
  (*the joint invariant*)
  invFG :: "state set"
  where "invFG = {s. NG s <= NF s & NF s <= Suc (NG s) & (BB s = (NF s = NG s))}"


declare F_def [THEN def_prg_Init, simp] 
        G_def [THEN def_prg_Init, simp]

        cmdF_def [THEN def_act_simp, simp]
        cmdG_def [THEN def_act_simp, simp]

        invFG_def [THEN def_set_simp, simp]


lemma invFG: "(F \<squnion> G) \<in> Always invFG"
apply (rule AlwaysI)
apply force
apply (rule constrains_imp_Constrains [THEN StableI])
apply auto
 apply (unfold F_def, safety) 
apply (unfold G_def, safety) 
done

lemma lemma2_1: "(F \<squnion> G) \<in> ({s. NF s = k} - {s. BB s}) LeadsTo  
                              ({s. NF s = k} Int {s. BB s})"
apply (rule stable_Join_ensures1[THEN leadsTo_Basis, THEN leadsTo_imp_LeadsTo])
 apply (unfold F_def, safety) 
apply (unfold G_def, ensures_tac "cmdG") 
done

lemma lemma2_2: "(F \<squnion> G) \<in> ({s. NF s = k} Int {s. BB s}) LeadsTo 
                              {s. k < NF s}"
apply (rule stable_Join_ensures2[THEN leadsTo_Basis, THEN leadsTo_imp_LeadsTo])
 apply (unfold F_def, ensures_tac "cmdF") 
apply (unfold G_def, safety) 
done

lemma progress: "(F \<squnion> G) \<in> UNIV LeadsTo {s. m < NF s}"
apply (rule LeadsTo_weaken_R)
apply (rule_tac f = "NF" and l = "Suc m" and B = "{}" 
       in GreaterThan_bounded_induct)
(*The inductive step is (F \<squnion> G) : {x. NF x = ma} LeadsTo {x. ma < NF x}*)
apply (auto intro!: lemma2_1 lemma2_2
            intro: LeadsTo_Trans LeadsTo_Diff simp add: vimage_def)
done

end
