(*  Title:      HOL/Library/Continuity.thy
    ID:         $$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

*)

header {*
  \title{Continuity and interations (of set transformers)}
  \author{David von Oheimb}
*}

theory Continuity = Relation_Power:


subsection "Chains"

constdefs
  up_chain      :: "(nat => 'a set) => bool"
 "up_chain F      == !i. F i <= F (Suc i)"

lemma up_chainI: "(!!i. F i <= F (Suc i)) ==> up_chain F"
by (simp add: up_chain_def);

lemma up_chainD: "up_chain F ==> F i <= F (Suc i)"
by (simp add: up_chain_def);

lemma up_chain_less_mono [rule_format]: "up_chain F ==> x < y --> F x <= F y"
apply (induct_tac y)
apply (blast dest: up_chainD elim: less_SucE)+
done

lemma up_chain_mono: "up_chain F ==> x <= y ==> F x <= F y"
apply (drule le_imp_less_or_eq)
apply (blast dest: up_chain_less_mono)
done


constdefs
  down_chain      :: "(nat => 'a set) => bool"
 "down_chain F == !i. F (Suc i) <= F i"

lemma down_chainI: "(!!i. F (Suc i) <= F i) ==> down_chain F"
by (simp add: down_chain_def);

lemma down_chainD: "down_chain F ==> F (Suc i) <= F i"
by (simp add: down_chain_def);

lemma down_chain_less_mono[rule_format]: "down_chain F ==> x < y --> F y <= F x"
apply (induct_tac y)
apply (blast dest: down_chainD elim: less_SucE)+
done

lemma down_chain_mono: "down_chain F ==> x <= y ==> F y <= F x"
apply (drule le_imp_less_or_eq)
apply (blast dest: down_chain_less_mono)
done


subsection "Continuity"

constdefs
  up_cont :: "('a set => 'a set) => bool"
 "up_cont f == !F. up_chain F --> f (Union (range F)) = Union (f`(range F))"

lemma up_contI: 
 "(!!F. up_chain F ==> f (Union (range F)) = Union (f`(range F))) ==> up_cont f"
apply (unfold up_cont_def)
by blast

lemma up_contD: 
  "[| up_cont f; up_chain F |] ==> f (Union (range F)) = Union (f`(range F))"
apply (unfold up_cont_def)
by auto


lemma up_cont_mono: "up_cont f ==> mono f"
apply (rule monoI)
apply (drule_tac F = "%i. if i = 0 then A else B" in up_contD)
apply  (rule up_chainI)
apply  simp+
apply (drule Un_absorb1)
apply auto
done


constdefs
  down_cont :: "('a set => 'a set) => bool"
 "down_cont f == !F. down_chain F --> f (Inter (range F)) = Inter (f`(range F))"

lemma down_contI: 
 "(!!F. down_chain F ==> f (Inter (range F)) = Inter (f`(range F))) ==> 
  down_cont f"
apply (unfold down_cont_def)
by blast

lemma down_contD: "[| down_cont f; down_chain F |] ==> 
  f (Inter (range F)) = Inter (f`(range F))"
apply (unfold down_cont_def)
by auto

lemma down_cont_mono: "down_cont f ==> mono f"
apply (rule monoI)
apply (drule_tac F = "%i. if i = 0 then B else A" in down_contD)
apply  (rule down_chainI)
apply  simp+
apply (drule Int_absorb1)
apply auto
done


subsection "Iteration"

constdefs

  up_iterate :: "('a set => 'a set) => nat => 'a set"
 "up_iterate f n == (f^n) {}"

lemma up_iterate_0 [simp]: "up_iterate f 0 = {}"
by (simp add: up_iterate_def)

lemma up_iterate_Suc [simp]: 
  "up_iterate f (Suc i) = f (up_iterate f i)"
by (simp add: up_iterate_def)

lemma up_iterate_chain: "mono F ==> up_chain (up_iterate F)"
apply (rule up_chainI)
apply (induct_tac i)
apply simp+
apply (erule (1) monoD)
done

lemma UNION_up_iterate_is_fp: 
"up_cont F ==> F (UNION UNIV (up_iterate F)) = UNION UNIV (up_iterate F)"
apply (frule up_cont_mono [THEN up_iterate_chain])
apply (drule (1) up_contD)
apply simp
apply (auto simp del: up_iterate_Suc simp add: up_iterate_Suc [symmetric])
apply (case_tac "xa")
apply auto
done

lemma UNION_up_iterate_lowerbound: 
"[| mono F; F P = P |] ==> UNION UNIV (up_iterate F) <= P"
apply (subgoal_tac "(!!i. up_iterate F i <= P)")
apply  fast
apply (induct_tac "i")
prefer 2 apply (drule (1) monoD)
apply auto
done

lemma UNION_up_iterate_is_lfp: 
  "up_cont F ==> lfp F = UNION UNIV (up_iterate F)"
apply (rule set_eq_subset [THEN iffD2])
apply (rule conjI)
prefer 2
apply  (drule up_cont_mono)
apply  (rule UNION_up_iterate_lowerbound)
apply   assumption
apply  (erule lfp_unfold [symmetric])
apply (rule lfp_lowerbound)
apply (rule set_eq_subset [THEN iffD1, THEN conjunct2])
apply (erule UNION_up_iterate_is_fp [symmetric])
done


constdefs

  down_iterate :: "('a set => 'a set) => nat => 'a set"
 "down_iterate f n == (f^n) UNIV"

lemma down_iterate_0 [simp]: "down_iterate f 0 = UNIV"
by (simp add: down_iterate_def)

lemma down_iterate_Suc [simp]: 
  "down_iterate f (Suc i) = f (down_iterate f i)"
by (simp add: down_iterate_def)

lemma down_iterate_chain: "mono F ==> down_chain (down_iterate F)"
apply (rule down_chainI)
apply (induct_tac i)
apply simp+
apply (erule (1) monoD)
done

lemma INTER_down_iterate_is_fp: 
"down_cont F ==> 
 F (INTER UNIV (down_iterate F)) = INTER UNIV (down_iterate F)"
apply (frule down_cont_mono [THEN down_iterate_chain])
apply (drule (1) down_contD)
apply simp
apply (auto simp del: down_iterate_Suc simp add: down_iterate_Suc [symmetric])
apply (case_tac "xa")
apply auto
done

lemma INTER_down_iterate_upperbound: 
"[| mono F; F P = P |] ==> P <= INTER UNIV (down_iterate F)"
apply (subgoal_tac "(!!i. P <= down_iterate F i)")
apply  fast
apply (induct_tac "i")
prefer 2 apply (drule (1) monoD)
apply auto
done

lemma INTER_down_iterate_is_gfp: 
  "down_cont F ==> gfp F = INTER UNIV (down_iterate F)"
apply (rule set_eq_subset [THEN iffD2])
apply (rule conjI)
apply  (drule down_cont_mono)
apply  (rule INTER_down_iterate_upperbound)
apply   assumption
apply  (erule gfp_unfold [symmetric])
apply (rule gfp_upperbound)
apply (rule set_eq_subset [THEN iffD1, THEN conjunct2])
apply (erule INTER_down_iterate_is_fp)
done

end
