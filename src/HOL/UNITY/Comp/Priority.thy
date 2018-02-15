(*  Title:      HOL/UNITY/Comp/Priority.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section\<open>The priority system\<close>

theory Priority imports PriorityAux begin

text\<open>From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.\<close>

type_synonym state = "(vertex*vertex)set"
type_synonym command = "vertex=>(state*state)set"
  
consts
  init :: "(vertex*vertex)set"  
  \<comment> \<open>the initial state\<close>

text\<open>Following the definitions given in section 4.4\<close>

definition highest :: "[vertex, (vertex*vertex)set]=>bool"
  where "highest i r \<longleftrightarrow> A i r = {}"
    \<comment> \<open>i has highest priority in r\<close>
  
definition lowest :: "[vertex, (vertex*vertex)set]=>bool"
  where "lowest i r \<longleftrightarrow> R i r = {}"
    \<comment> \<open>i has lowest priority in r\<close>

definition act :: command
  where "act i = {(s, s'). s'=reverse i s & highest i s}"

definition Component :: "vertex=>state program"
  where "Component i = mk_total_program({init}, {act i}, UNIV)"
    \<comment> \<open>All components start with the same initial state\<close>


text\<open>Some Abbreviations\<close>
definition Highest :: "vertex=>state set"
  where "Highest i = {s. highest i s}"

definition Lowest :: "vertex=>state set"
  where "Lowest i = {s. lowest i s}"

definition Acyclic :: "state set"
  where "Acyclic = {s. acyclic s}"


definition Maximal :: "state set"
    \<comment> \<open>Every ``above'' set has a maximal vertex\<close>
  where "Maximal = (\<Inter>i. {s. ~highest i s-->(\<exists>j \<in> above i  s. highest j s)})"

definition Maximal' :: "state set"
    \<comment> \<open>Maximal vertex: equivalent definition\<close>
  where "Maximal' = (\<Inter>i. Highest i Un (\<Union>j. {s. j \<in> above i s} Int Highest j))"

  
definition Safety :: "state set"
  where "Safety = (\<Inter>i. {s. highest i s --> (\<forall>j \<in> neighbors i s. ~highest j s)})"


  (* Composition of a finite set of component;
     the vertex 'UNIV' is finite by assumption *)
  
definition system :: "state program"
  where "system = (\<Squnion>i. Component i)"


declare highest_def [simp] lowest_def [simp]
declare Highest_def [THEN def_set_simp, simp] 
    and Lowest_def  [THEN def_set_simp, simp]

declare Component_def [THEN def_prg_Init, simp]
declare act_def [THEN def_act_simp, simp]



subsection\<open>Component correctness proofs\<close>

text\<open>neighbors is stable\<close>
lemma Component_neighbors_stable: "Component i \<in> stable {s. neighbors k s = n}"
by (simp add: Component_def, safety, auto)

text\<open>property 4\<close>
lemma Component_waits_priority: "Component i \<in> {s. ((i,j) \<in> s) = b} \<inter> (- Highest i) co {s. ((i,j) \<in> s)=b}"
by (simp add: Component_def, safety)

text\<open>property 5: charpentier and Chandy mistakenly express it as
 'transient Highest i'. Consider the case where i has neighbors\<close>
lemma Component_yields_priority: 
 "Component i \<in> {s. neighbors i s \<noteq> {}} Int Highest i  
               ensures - Highest i"
apply (simp add: Component_def)
apply (ensures_tac "act i", blast+) 
done

text\<open>or better\<close>
lemma Component_yields_priority': "Component i \<in> Highest i ensures Lowest i"
apply (simp add: Component_def)
apply (ensures_tac "act i", blast+) 
done

text\<open>property 6: Component doesn't introduce cycle\<close>
lemma Component_well_behaves: "Component i \<in> Highest i co Highest i Un Lowest i"
by (simp add: Component_def, safety, fast)

text\<open>property 7: local axiom\<close>
lemma locality: "Component i \<in> stable {s. \<forall>j k. j\<noteq>i & k\<noteq>i--> ((j,k) \<in> s) = b j k}"
by (simp add: Component_def, safety)


subsection\<open>System  properties\<close>
text\<open>property 8: strictly universal\<close>

lemma Safety: "system \<in> stable Safety"
apply (unfold Safety_def)
apply (rule stable_INT)
apply (simp add: system_def, safety, fast)
done

text\<open>property 13: universal\<close>
lemma p13: "system \<in> {s. s = q} co {s. s=q} Un {s. \<exists>i. derive i q s}"
by (simp add: system_def Component_def mk_total_program_def totalize_JN, safety, blast)

text\<open>property 14: the 'above set' of a Component that hasn't got 
      priority doesn't increase\<close>
lemma above_not_increase: 
     "system \<in> -Highest i Int {s. j\<notin>above i s} co {s. j\<notin>above i s}"
apply (insert reach_lemma [of concl: j])
apply (simp add: system_def Component_def mk_total_program_def totalize_JN, 
       safety)
apply (simp add: trancl_converse, blast) 
done

lemma above_not_increase':
     "system \<in> -Highest i Int {s. above i s = x} co {s. above i s <= x}"
apply (insert above_not_increase [of i])
apply (simp add: trancl_converse constrains_def, blast)
done



text\<open>p15: universal property: all Components well behave\<close>
lemma system_well_behaves: "system \<in> Highest i co Highest i Un Lowest i"
  by (simp add: system_def Component_def mk_total_program_def totalize_JN, safety, auto)


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

text\<open>property 17: original one is an invariant\<close>
lemma Acyclic_Maximal_stable: "system \<in> stable (Acyclic Int Maximal)"
by (simp add: Acyclic_subset_Maximal [THEN Int_absorb2] Acyclic_stable)


text\<open>property 5: existential property\<close>

lemma Highest_leadsTo_Lowest: "system \<in> Highest i leadsTo Lowest i"
apply (simp add: system_def Component_def mk_total_program_def totalize_JN)
apply (ensures_tac "act i", auto)
done

text\<open>a lowest i can never be in any abover set\<close> 
lemma Lowest_above_subset: "Lowest i <= (\<Inter>k. {s. i\<notin>above k s})"
by (auto simp add: image0_r_iff_image0_trancl trancl_converse)

text\<open>property 18: a simpler proof than the original, one which uses psp\<close>
lemma Highest_escapes_above: "system \<in> Highest i leadsTo (\<Inter>k. {s. i\<notin>above k s})"
apply (rule leadsTo_weaken_R)
apply (rule_tac [2] Lowest_above_subset)
apply (rule Highest_leadsTo_Lowest)
done

lemma Highest_escapes_above':
     "system \<in> Highest j Int {s. j \<in> above i s} leadsTo {s. j\<notin>above i s}"
by (blast intro: leadsTo_weaken [OF Highest_escapes_above Int_lower1 INT_lower])

subsection\<open>The main result: above set decreases\<close>

text\<open>The original proof of the following formula was wrong\<close>

lemma Highest_iff_above0: "Highest i = {s. above i s ={}}"
by (auto simp add: image0_trancl_iff_image0_r)

lemmas above_decreases_lemma = 
     psp [THEN leadsTo_weaken, OF Highest_escapes_above' above_not_increase'] 


lemma above_decreases: 
     "system \<in> (\<Union>j. {s. above i s = x} Int {s. j \<in> above i s} Int Highest j)  
               leadsTo {s. above i s < x}"
apply (rule leadsTo_UN)
apply (rule single_leadsTo_I, clarify)
apply (rule_tac x = "above i xa" in above_decreases_lemma)
apply (simp_all (no_asm_use) add: Highest_iff_above0)
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
apply (simp del: above_def
            add: Highest_iff_above0 vimage_def finite_psubset_def, clarify)
apply (case_tac "m={}")
apply (rule Int_lower2 [THEN [2] leadsTo_weaken_L])
apply (force simp add: leadsTo_refl)
apply (rule_tac A' = "Acyclic Int {x. above i x < m}" in leadsTo_weaken_R)
apply (blast intro: above_decreases_psp')+
done


text\<open>We have proved all (relevant) theorems given in the paper.  We didn't
assume any thing about the relation @{term r}.  It is not necessary that
@{term r} be a priority relation as assumed in the original proof.  It
suffices that we start from a state which is finite and acyclic.\<close>


end
