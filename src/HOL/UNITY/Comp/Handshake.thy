(*  Title:      HOL/UNITY/Handshake.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Handshake Protocol

From Misra, "Asynchronous Compositions of Programs", Section 5.3.2
*)

theory Handshake = UNITY_Main:

record state =
  BB :: bool
  NF :: nat
  NG :: nat

constdefs
  (*F's program*)
  cmdF :: "(state*state) set"
    "cmdF == {(s,s'). s' = s (|NF:= Suc(NF s), BB:=False|) & BB s}"

  F :: "state program"
    "F == mk_program ({s. NF s = 0 & BB s}, {cmdF}, UNIV)"

  (*G's program*)
  cmdG :: "(state*state) set"
    "cmdG == {(s,s'). s' = s (|NG:= Suc(NG s), BB:=True|) & ~ BB s}"

  G :: "state program"
    "G == mk_program ({s. NG s = 0 & BB s}, {cmdG}, UNIV)"

  (*the joint invariant*)
  invFG :: "state set"
    "invFG == {s. NG s <= NF s & NF s <= Suc (NG s) & (BB s = (NF s = NG s))}"


declare F_def [THEN def_prg_Init, simp] 
        G_def [THEN def_prg_Init, simp]

        cmdF_def [THEN def_act_simp, simp]
        cmdG_def [THEN def_act_simp, simp]

        invFG_def [THEN def_set_simp, simp]


lemma invFG: "(F Join G) : Always invFG"
apply (rule AlwaysI)
apply force
apply (rule constrains_imp_Constrains [THEN StableI])
apply auto
 apply (unfold F_def, constrains) 
apply (unfold G_def, constrains) 
done

lemma lemma2_1: "(F Join G) : ({s. NF s = k} - {s. BB s}) LeadsTo  
                              ({s. NF s = k} Int {s. BB s})"
apply (rule stable_Join_ensures1[THEN leadsTo_Basis, THEN leadsTo_imp_LeadsTo])
 apply (unfold F_def, constrains) 
apply (unfold G_def, ensures_tac "cmdG") 
done

lemma lemma2_2: "(F Join G) : ({s. NF s = k} Int {s. BB s}) LeadsTo 
                              {s. k < NF s}"
apply (rule stable_Join_ensures2[THEN leadsTo_Basis, THEN leadsTo_imp_LeadsTo])
 apply (unfold F_def, ensures_tac "cmdF") 
apply (unfold G_def, constrains) 
done

lemma progress: "(F Join G) : UNIV LeadsTo {s. m < NF s}"
apply (rule LeadsTo_weaken_R)
apply (rule_tac f = "NF" and l = "Suc m" and B = "{}" 
       in GreaterThan_bounded_induct)
(*The inductive step is (F Join G) : {x. NF x = ma} LeadsTo {x. ma < NF x}*)
apply (auto intro!: lemma2_1 lemma2_2
            intro: LeadsTo_Trans LeadsTo_Diff simp add: vimage_def)
done

end
