(*  Title:      HOL/Alethe_Rare_Interface.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Rare_Interface
  imports "Alethe_Boolean_Rewrites" "Alethe_Builtin_Rewrites" "Alethe_Arith_Rewrites" "Alethe_UF_Rewrites" "Alethe_cvc5_Rewrites"
  keywords
    "cvc5_rare" :: thy_decl
begin


subsection \<open>Parse arguments\<close>

ML \<open>
(*alethe proofs can contain rare_rewrites. The arguments may use rare-list to express lists.*)
fun alethe_term_parser (SMTLIB.Sym "rare-list", []) = (
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const(\<^const_name>\<open>ListVar\<close>, dummyT --> dummyT) $ Const(\<^const_name>\<open>List.Nil\<close>, dummyT)))
| alethe_term_parser (SMTLIB.Sym "rare-list", ts) = (
  let
    val new_type = fastype_of (hd ts)
  in
    SOME(Const(\<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[new_type]) --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[new_type]))
    $ (HOLogic.mk_list new_type ts))
  end)
| alethe_term_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser alethe_term_parser)
)\<close>

subsection \<open>Replay rare_rules\<close>

ML_file \<open>Tools/SMT/alethe/rare_rewrites/cvc5_rare.ML\<close>



subsection \<open>Register rare_rules\<close>

(*Arithmetic*)
(*Some rules are defined in Alethe_Rare_Interface_Real, others are omitted when including operators
we don't use.*)
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_elim_gt"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_elim_lt"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_elim_int_gt"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_elim_int_lt"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_elim_leq"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_leq_norm"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_geq_tighten"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_geq_norm1_int"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_eq_elim_int"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_mod_over_mod"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_divisible_elim"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_geq_ite_lift"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_leq_ite_lift"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_min_lt1"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_min_lt2"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_max_geq1"
cvc5_rare "Alethe_Arith_Rewrites.rewrite_arith_max_geq2"

(*Booleans*)
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_double_not_elim"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_not_true"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_not_false"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_eq_true"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_eq_false"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_eq_nrefl"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_impl_false1"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_impl_false2"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_impl_true1"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_impl_true2"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_impl_elim"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_dual_impl_eq"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_and_conf"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_and_conf2"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_or_taut"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_or_taut2"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_or_de_morgan"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_implies_de_morgan"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_and_de_morgan"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_or_and_distrib"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_implies_or_distrib"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_xor_refl"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_xor_nrefl"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_xor_false"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_xor_true"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_xor_comm"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_xor_elim"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_not_xor_elim"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_not_eq_elim1"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_not_eq_elim2"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_neg_branch"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_then_true"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_else_false"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_then_false"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_else_true"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_then_lookahead_self"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_else_lookahead_self"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_then_lookahead_not_self"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_else_lookahead_not_self"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_ite_expand"
cvc5_rare "Alethe_Boolean_Rewrites.rewrite_bool_not_ite_elim"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_true_cond"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_false_cond"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_not_cond"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_eq_branch"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_then_lookahead"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_else_lookahead"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_then_neg_lookahead"
cvc5_rare "Alethe_Builtin_Rewrites.rewrite_ite_else_neg_lookahead"

(*Uninterpreted Functions*)
cvc5_rare "Alethe_UF_Rewrites.rewrite_eq_refl"
cvc5_rare "Alethe_UF_Rewrites.rewrite_eq_symm"
cvc5_rare "Alethe_UF_Rewrites.rewrite_eq_cond_deq"
cvc5_rare "Alethe_UF_Rewrites.rewrite_eq_ite_lift"
cvc5_rare "Alethe_UF_Rewrites.rewrite_distinct_binary_elim"

(*cvc5 only*)
cvc5_rare "Alethe_cvc5_Rewrites.rewrite_ite_eq"
cvc5_rare "Alethe_cvc5_Rewrites.rewrite_or_not_refl"

ML_file \<open>Tools/SMT/alethe/rare_rewrites/alethe_replay_rare_simplify_methods.ML\<close>

end
