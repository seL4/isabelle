theory Predicate_Compile_Alternative_Defs
imports Main
begin

section {* Set operations *}
(*
definition Empty where "Empty == {}"
declare empty_def[symmetric, code_pred_inline]
*)
declare eq_reflection[OF empty_def, code_pred_inline] 
(*
definition Union where "Union A B == A Un B"

lemma [code_pred_intros]: "A x ==> Union A B x"
and  [code_pred_intros] : "B x ==> Union A B x"
unfolding Union_def Un_def Collect_def mem_def by auto

code_pred Union
unfolding Union_def Un_def Collect_def mem_def by auto

declare Union_def[symmetric, code_pred_inline]
*)
declare eq_reflection[OF Un_def, code_pred_inline]

section {* Alternative list definitions *}
 
subsection {* Alternative rules for set *}

lemma set_ConsI1 [code_pred_intros]:
  "set (x # xs) x"
unfolding mem_def[symmetric, of _ x]
by auto

lemma set_ConsI2 [code_pred_intros]:
  "set xs x ==> set (x' # xs) x" 
unfolding mem_def[symmetric, of _ x]
by auto

code_pred set
proof -
  case set
  from this show thesis
    apply (case_tac a1)
    apply auto
    unfolding mem_def[symmetric, of _ a2]
    apply auto
    unfolding mem_def
    apply auto
    done
qed


subsection {* Alternative rules for list_all2 *}

lemma list_all2_NilI [code_pred_intros]: "list_all2 P [] []"
by auto

lemma list_all2_ConsI [code_pred_intros]: "list_all2 P xs ys ==> P x y ==> list_all2 P (x#xs) (y#ys)"
by auto

code_pred list_all2
proof -
  case list_all2
  from this show thesis
    apply -
    apply (case_tac a1)
    apply (case_tac a2)
    apply auto
    apply (case_tac a2)
    apply auto
    done
qed



end