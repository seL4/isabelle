(*  Title:      HOL/Complex/ex/BigO_Complex.thy
    ID:		$Id$
    Authors:    Jeremy Avigad and Kevin Donnelly
*)

header {* Big O notation -- continued *}

theory BigO_Complex
imports BigO Complex
begin

text {*
  Additional lemmas that require the \texttt{HOL-Complex} logic image.
*}

lemma bigo_LIMSEQ1: "f =o O(g) ==> g ----> 0 ==> f ----> 0"
  apply (simp add: LIMSEQ_def bigo_alt_def)
  apply clarify
  apply (drule_tac x = "r / c" in spec)
  apply (drule mp)
  apply (erule divide_pos_pos)
  apply assumption
  apply clarify
  apply (rule_tac x = no in exI)
  apply (rule allI)
  apply (drule_tac x = n in spec)+
  apply (rule impI)
  apply (drule mp)
  apply assumption
  apply (rule order_le_less_trans)
  apply assumption
  apply (rule order_less_le_trans)
  apply (subgoal_tac "c * abs(g n) < c * (r / c)")
  apply assumption
  apply (erule mult_strict_left_mono)
  apply assumption
  apply simp
done

lemma bigo_LIMSEQ2: "f =o g +o O(h) ==> h ----> 0 ==> f ----> a 
    ==> g ----> a"
  apply (drule set_plus_imp_minus)
  apply (drule bigo_LIMSEQ1)
  apply assumption
  apply (simp only: func_diff)
  apply (erule LIMSEQ_diff_approach_zero2)
  apply assumption
done

end
