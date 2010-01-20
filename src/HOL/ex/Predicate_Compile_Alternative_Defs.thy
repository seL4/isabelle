theory Predicate_Compile_Alternative_Defs
imports "../Predicate_Compile"
begin

section {* Set operations *}

declare Collect_def[code_pred_inline]
declare mem_def[code_pred_inline]

declare eq_reflection[OF empty_def, code_pred_inline]
declare insert_code[code_pred_def]
declare eq_reflection[OF Un_def, code_pred_inline]
declare eq_reflection[OF UNION_def, code_pred_inline]



section {* Alternative list definitions *}
 
subsection {* Alternative rules for set *}

lemma set_ConsI1 [code_pred_intro]:
  "set (x # xs) x"
unfolding mem_def[symmetric, of _ x]
by auto

lemma set_ConsI2 [code_pred_intro]:
  "set xs x ==> set (x' # xs) x" 
unfolding mem_def[symmetric, of _ x]
by auto

code_pred [skip_proof] set
proof -
  case set
  from this show thesis
    apply (case_tac xb)
    apply auto
    unfolding mem_def[symmetric, of _ xc]
    apply auto
    unfolding mem_def
    apply fastsimp
    done
qed

subsection {* Alternative rules for list_all2 *}

lemma list_all2_NilI [code_pred_intro]: "list_all2 P [] []"
by auto

lemma list_all2_ConsI [code_pred_intro]: "list_all2 P xs ys ==> P x y ==> list_all2 P (x#xs) (y#ys)"
by auto

code_pred [skip_proof] list_all2
proof -
  case list_all2
  from this show thesis
    apply -
    apply (case_tac xa)
    apply (case_tac xb)
    apply auto
    apply (case_tac xb)
    apply auto
    done
qed



end