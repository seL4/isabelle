theory Predicate_Compile
imports Complex_Main RPred
uses
  "../Tools/Predicate_Compile/pred_compile_aux.ML"
  "../Tools/Predicate_Compile/predicate_compile_core.ML"
  "../Tools/Predicate_Compile/pred_compile_set.ML"
  "../Tools/Predicate_Compile/pred_compile_data.ML"
  "../Tools/Predicate_Compile/pred_compile_fun.ML"
  "../Tools/Predicate_Compile/pred_compile_pred.ML"
  "../Tools/Predicate_Compile/predicate_compile.ML"
  "../Tools/Predicate_Compile/pred_compile_quickcheck.ML"
begin

setup {* Predicate_Compile.setup *}
setup {* Quickcheck.add_generator ("pred_compile", Pred_Compile_Quickcheck.quickcheck) *}

section {* Alternative rules for set *}

lemma set_ConsI1 [code_pred_intros]:
  "set (x # xs) x"
unfolding mem_def[symmetric, of _ x]
by auto

lemma set_ConsI2 [code_pred_intros]:
  "set xs x ==> set (x' # xs) x" 
unfolding mem_def[symmetric, of _ x]
by auto
(*
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
*)

section {* Alternative rules for list_all2 *}

lemma list_all2_NilI [code_pred_intros]: "list_all2 P [] []"
by auto

lemma list_all2_ConsI [code_pred_intros]: "list_all2 P xs ys ==> P x y ==> list_all2 P (x#xs) (y#ys)"
by auto

(*
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
*)
end