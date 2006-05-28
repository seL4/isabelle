(*  Title:      HOLCF/IOA/meta_theory/Compositionality.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Compositionality of I/O automata *}
theory Compositionality
imports CompoTraces
begin

lemma compatibility_consequence3: "[|eA --> A ; eB & ~eA --> ~A|] ==> (eA | eB) --> A=eA"
apply auto
done


lemma Filter_actAisFilter_extA: 
"!! A B. [| compatible A B; Forall (%a. a: ext A | a: ext B) tr |] ==>  
            Filter (%a. a: act A)$tr= Filter (%a. a: ext A)$tr"
apply (rule ForallPFilterQR)
(* i.e.: [| (! x. P x --> (Q x = R x)) ; Forall P tr |] ==> Filter Q$tr = Filter R$tr *)
prefer 2 apply (assumption)
apply (rule compatibility_consequence3)
apply (simp_all add: ext_is_act ext1_ext2_is_not_act1)
done


(* the next two theorems are only necessary, as there is no theorem ext (A||B) = ext (B||A) *)

lemma compatibility_consequence4: "[|eA --> A ; eB & ~eA --> ~A|] ==> (eB | eA) --> A=eA"
apply auto
done

lemma Filter_actAisFilter_extA2: "[| compatible A B; Forall (%a. a: ext B | a: ext A) tr |] ==>  
            Filter (%a. a: act A)$tr= Filter (%a. a: ext A)$tr"
apply (rule ForallPFilterQR)
prefer 2 apply (assumption)
apply (rule compatibility_consequence4)
apply (simp_all add: ext_is_act ext1_ext2_is_not_act1)
done


subsection " Main Compositionality Theorem "

lemma compositionality: "[| is_trans_of A1; is_trans_of A2; is_trans_of B1; is_trans_of B2; 
             is_asig_of A1; is_asig_of A2;  
             is_asig_of B1; is_asig_of B2;  
             compatible A1 B1; compatible A2 B2;  
             A1 =<| A2;  
             B1 =<| B2 |]  
         ==> (A1 || B1) =<| (A2 || B2)"
apply (simp add: is_asig_of_def)
apply (frule_tac A1 = "A1" in compat_commute [THEN iffD1])
apply (frule_tac A1 = "A2" in compat_commute [THEN iffD1])
apply (simp add: ioa_implements_def inputs_of_par outputs_of_par externals_of_par)
apply (tactic "safe_tac set_cs")
apply (simp add: compositionality_tr)
apply (subgoal_tac "ext A1 = ext A2 & ext B1 = ext B2")
prefer 2
apply (simp add: externals_def)
apply (erule conjE)+
(* rewrite with proven subgoal *)
apply (simp add: externals_of_par)
apply (tactic "safe_tac set_cs")

(* 2 goals, the 3rd has been solved automatically *)
(* 1: Filter A2 x : traces A2 *)
apply (drule_tac A = "traces A1" in subsetD)
apply assumption
apply (simp add: Filter_actAisFilter_extA)
(* 2: Filter B2 x : traces B2 *)
apply (drule_tac A = "traces B1" in subsetD)
apply assumption
apply (simp add: Filter_actAisFilter_extA2)
done

end
