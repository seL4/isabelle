theory Predicate_Compile_Alternative_Defs
imports "../Predicate_Compile"
begin

section {* Common constants *}

declare HOL.if_bool_eq_disj[code_pred_inline]

setup {* Predicate_Compile_Data.ignore_consts [@{const_name Let}] *}

section {* Pairs *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name fst}, @{const_name snd}, @{const_name split}] *}

section {* Bounded quantifiers *}

declare Ball_def[code_pred_inline]
declare Bex_def[code_pred_inline]

section {* Set operations *}

declare Collect_def[code_pred_inline]
declare mem_def[code_pred_inline]

declare eq_reflection[OF empty_def, code_pred_inline]
declare insert_code[code_pred_def]

declare subset_iff[code_pred_inline]

declare Int_def[code_pred_inline]
declare eq_reflection[OF Un_def, code_pred_inline]
declare eq_reflection[OF UNION_def, code_pred_inline]

lemma Diff[code_pred_inline]:
  "(A - B) = (%x. A x \<and> \<not> B x)"
by (auto simp add: mem_def)

lemma set_equality[code_pred_inline]:
  "(A = B) = ((\<forall>x. A x \<longrightarrow> B x) \<and> (\<forall>x. B x \<longrightarrow> A x))"
by (fastsimp simp add: mem_def)

section {* Setup for Numerals *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name number_of}] *}
setup {* Predicate_Compile_Data.keep_functions [@{const_name number_of}] *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name div}, @{const_name mod}, @{const_name times}] *}

section {* Alternative list definitions *}

text {* size simps are not yet added to the Spec_Rules interface. So they are just added manually here! *}
 
lemma [code_pred_def]:
  "length [] = 0"
  "length (x # xs) = Suc (length xs)"
by auto

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
    apply (case_tac xb)
    apply (case_tac xc)
    apply auto
    apply (case_tac xc)
    apply auto
    apply fastsimp
    done
qed



end