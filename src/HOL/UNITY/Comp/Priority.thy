(*  Title:      HOL/UNITY/Priority
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge


*)

header{*The priority system*}

theory Priority = PriorityAux:

text{*From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.*}

types state = "(vertex*vertex)set"
types command = "vertex=>(state*state)set"
  
consts
  (* the initial state *)
  init :: "(vertex*vertex)set"  

constdefs
  (* from the definitions given in section 4.4 *)
  (* i has highest priority in r *)
  highest :: "[vertex, (vertex*vertex)set]=>bool"
  "highest i r == A i r = {}"
  
  (* i has lowest priority in r *)
  lowest :: "[vertex, (vertex*vertex)set]=>bool"
  "lowest i r == R i r = {}"

  act :: command
  "act i == {(s, s'). s'=reverse i s & highest i s}"

  (* All components start with the same initial state *)
  Component :: "vertex=>state program"
  "Component i == mk_total_program({init}, {act i}, UNIV)"

  (* Abbreviations *)
  Highest :: "vertex=>state set"
  "Highest i == {s. highest i s}"

  Lowest :: "vertex=>state set"
  "Lowest i == {s. lowest i s}"

  Acyclic :: "state set"
  "Acyclic == {s. acyclic s}"

  (* Every above set has a maximal vertex: two equivalent defs. *)

  Maximal :: "state set"
  "Maximal == \<Inter>i. {s. ~highest i s-->(\<exists>j \<in> above i  s. highest j s)}"

  Maximal' :: "state set"
  "Maximal' == \<Inter>i. Highest i Un (\<Union>j. {s. j \<in> above i s} Int Highest j)"

  
  Safety :: "state set"
  "Safety == \<Inter>i. {s. highest i s --> (\<forall>j \<in> neighbors i s. ~highest j s)}"


  (* Composition of a finite set of component;
     the vertex 'UNIV' is finite by assumption *)
  
  system :: "state program"
  "system == JN i. Component i"


declare highest_def [simp] lowest_def [simp]
declare Highest_def [THEN def_set_simp, simp] 
    and Lowest_def  [THEN def_set_simp, simp]

declare Component_def [THEN def_prg_Init, simp]
declare act_def [THEN def_act_simp, simp]



subsection{*Component correctness proofs*}

(* neighbors is stable  *)
lemma Component_neighbors_stable: "Component i \<in> stable {s. neighbors k s = n}"
by (simp add: Component_def, constrains, auto)

(* property 4 *)
lemma Component_waits_priority: "Component i: {s. ((i,j):s) = b} Int (- Highest i) co {s. ((i,j):s)=b}"
by (simp add: Component_def, constrains)

(* property 5: charpentier and Chandy mistakenly express it as
 'transient Highest i'. Consider the case where i has neighbors *)
lemma Component_yields_priority: 
 "Component i: {s. neighbors i s \<noteq> {}} Int Highest i  
               ensures - Highest i"
apply (simp add: Component_def)
apply (ensures_tac "act i", blast+) 
done

(* or better *)
lemma Component_yields_priority': "Component i \<in> Highest i ensures Lowest i"
apply (simp add: Component_def)
apply (ensures_tac "act i", blast+) 
done

(* property 6: Component doesn't introduce cycle *)
lemma Component_well_behaves: "Component i \<in> Highest i co Highest i Un Lowest i"
by (simp add: Component_def, constrains, fast)

(* property 7: local axiom *)
lemma locality: "Component i \<in> stable {s. \<forall>j k. j\<noteq>i & k\<noteq>i--> ((j,k):s) = b j k}"
by (simp add: Component_def, constrains)


subsection{*System  properties*}
(* property 8: strictly universal *)

lemma Safety: "system \<in> stable Safety"
apply (unfold Safety_def)
apply (rule stable_INT)
apply (simp add: system_def, constrains, fast)
done

(* property 13: universal *)
lemma p13: "system \<in> {s. s = q} co {s. s=q} Un {s. \<exists>i. derive i q s}"
by (simp add: system_def Component_def mk_total_program_def totalize_JN, constrains, blast)

(* property 14: the 'above set' of a Component that hasn't got 
      priority doesn't increase *)
lemma above_not_increase: 
     "\<forall>j. system \<in> -Highest i Int {s. j\<notin>above i s} co {s. j\<notin>above i s}"
apply clarify
apply (cut_tac i = j in reach_lemma)
apply (simp add: system_def Component_def mk_total_program_def totalize_JN, 
       constrains)
apply (auto simp add: trancl_converse)
done

lemma above_not_increase':
     "system \<in> -Highest i Int {s. above i s = x} co {s. above i s <= x}"
apply (cut_tac i = i in above_not_increase)
apply (simp add: trancl_converse constrains_def, blast)
done



(* p15: universal property: all Components well behave  *)
lemma system_well_behaves [rule_format]:
     "\<forall>i. system \<in> Highest i co Highest i Un Lowest i"
apply clarify
apply (simp add: system_def Component_def mk_total_program_def totalize_JN, 
       constrains, auto)
done


lemma Acyclic_eq: "Acyclic = (\<Inter>i. {s. i\<notin>above i s})"
by (auto simp add: Acyclic_def acyclic_def trancl_converse)


lemmas system_co =
      constrains_Un [OF above_not_increase [rule_format] system_well_behaves] 

lemma Acyclic_stable: "system \<in> stable Acyclic"
apply (simp add: stable_def Acyclic_eq) 
apply (auto intro!: constrains_INT system_co [THEN constrains_weaken] 
            simp add: image0_r_iff_image0_trancl trancl_converse)
done


lemma Acyclic_subset_Maximal: "Acyclic <= Maximal"
apply (unfold Acyclic_def Maximal_def, clarify)
apply (drule above_lemma_b, auto)
done

(* property 17: original one is an invariant *)
lemma Acyclic_Maximal_stable: "system \<in> stable (Acyclic Int Maximal)"
apply (simp add: Acyclic_subset_Maximal [THEN Int_absorb2] Acyclic_stable)
done


(* propert 5: existential property *)

lemma Highest_leadsTo_Lowest: "system \<in> Highest i leadsTo Lowest i"
apply (simp add: system_def Component_def mk_total_program_def totalize_JN)
apply (ensures_tac "act i", auto)
done

(* a lowest i can never be in any abover set *) 
lemma Lowest_above_subset: "Lowest i <= (\<Inter>k. {s. i\<notin>above k s})"
by (auto simp add: image0_r_iff_image0_trancl trancl_converse)

(* property 18: a simpler proof than the original, one which uses psp *)
lemma Highest_escapes_above: "system \<in> Highest i leadsTo (\<Inter>k. {s. i\<notin>above k s})"
apply (rule leadsTo_weaken_R)
apply (rule_tac [2] Lowest_above_subset)
apply (rule Highest_leadsTo_Lowest)
done

lemma Highest_escapes_above':
     "system \<in> Highest j Int {s. j \<in> above i s} leadsTo {s. j\<notin>above i s}"
by (blast intro: leadsTo_weaken [OF Highest_escapes_above Int_lower1 INT_lower])

(*** The main result: above set decreases ***)
(* The original proof of the following formula was wrong *)

lemma Highest_iff_above0: "Highest i = {s. above i s ={}}"
by (auto simp add: image0_trancl_iff_image0_r)

lemmas above_decreases_lemma = 
     psp [THEN leadsTo_weaken, OF Highest_escapes_above' above_not_increase'] 


lemma above_decreases: 
     "system \<in> (\<Union>j. {s. above i s = x} Int {s. j \<in> above i s} Int Highest j)  
               leadsTo {s. above i s < x}"
apply (rule leadsTo_UN)
apply (rule single_leadsTo_I, clarify)
apply (rule_tac x2 = "above i x" in above_decreases_lemma)
apply (simp_all (no_asm_use) del: Highest_def add: Highest_iff_above0)
apply blast+
done

(** Just a massage of conditions to have the desired form ***)
lemma Maximal_eq_Maximal': "Maximal = Maximal'"
by (unfold Maximal_def Maximal'_def Highest_def, blast)

lemma Acyclic_subset:
   "x\<noteq>{} ==>  
    Acyclic Int {s. above i s = x} <=  
    (\<Union>j. {s. above i s = x} Int {s. j \<in> above i s} Int Highest j)"
apply (rule_tac B = "Maximal' Int {s. above i s = x}" in subset_trans)
apply (simp (no_asm) add: Maximal_eq_Maximal' [symmetric])
apply (blast intro: Acyclic_subset_Maximal [THEN subsetD])
apply (simp (no_asm) del: above_def add: Maximal'_def Highest_iff_above0)
apply blast
done

lemmas above_decreases' = leadsTo_weaken_L [OF above_decreases Acyclic_subset]
lemmas above_decreases_psp = psp_stable [OF above_decreases' Acyclic_stable]

lemma above_decreases_psp': 
"x\<noteq>{}==> system \<in> Acyclic Int {s. above i s = x} leadsTo 
                   Acyclic Int {s. above i s < x}"
by (erule above_decreases_psp [THEN leadsTo_weaken], blast, auto)


lemmas finite_psubset_induct = wf_finite_psubset [THEN leadsTo_wf_induct]


lemma Progress: "system \<in> Acyclic leadsTo Highest i"
apply (rule_tac f = "%s. above i s" in finite_psubset_induct)
apply (simp del: Highest_def above_def
            add: Highest_iff_above0 vimage_def finite_psubset_def, clarify)
apply (case_tac "m={}")
apply (rule Int_lower2 [THEN [2] leadsTo_weaken_L])
apply (force simp add: leadsTo_refl)
apply (rule_tac A' = "Acyclic Int {x. above i x < m}" in leadsTo_weaken_R)
apply (blast intro: above_decreases_psp')+
done


text{*We have proved all (relevant) theorems given in the paper.  We didn't
assume any thing about the relation @{term r}.  It is not necessary that
@{term r} be a priority relation as assumed in the original proof.  It
suffices that we start from a state which is finite and acyclic.*}


end