(*  Title:      HOL/UNITY/UNITY_tactics.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Specialized UNITY tactics, and ML bindings of theorems
*)

(*ListOrder*)
val Le_def = thm "Le_def";
val Ge_def = thm "Ge_def";
val prefix_def = thm "prefix_def";
val Nil_genPrefix = thm "Nil_genPrefix";
val genPrefix_length_le = thm "genPrefix_length_le";
val cons_genPrefixE = thm "cons_genPrefixE";
val Cons_genPrefix_Cons = thm "Cons_genPrefix_Cons";
val refl_genPrefix = thm "refl_genPrefix";
val genPrefix_refl = thm "genPrefix_refl";
val genPrefix_mono = thm "genPrefix_mono";
val append_genPrefix = thm "append_genPrefix";
val genPrefix_trans_O = thm "genPrefix_trans_O";
val genPrefix_trans = thm "genPrefix_trans";
val prefix_genPrefix_trans = thm "prefix_genPrefix_trans";
val genPrefix_prefix_trans = thm "genPrefix_prefix_trans";
val trans_genPrefix = thm "trans_genPrefix";
val genPrefix_antisym = thm "genPrefix_antisym";
val antisym_genPrefix = thm "antisym_genPrefix";
val genPrefix_Nil = thm "genPrefix_Nil";
val same_genPrefix_genPrefix = thm "same_genPrefix_genPrefix";
val genPrefix_Cons = thm "genPrefix_Cons";
val genPrefix_take_append = thm "genPrefix_take_append";
val genPrefix_append_both = thm "genPrefix_append_both";
val append_cons_eq = thm "append_cons_eq";
val append_one_genPrefix = thm "append_one_genPrefix";
val genPrefix_imp_nth = thm "genPrefix_imp_nth";
val nth_imp_genPrefix = thm "nth_imp_genPrefix";
val genPrefix_iff_nth = thm "genPrefix_iff_nth";
val prefix_refl = thm "prefix_refl";
val prefix_trans = thm "prefix_trans";
val prefix_antisym = thm "prefix_antisym";
val prefix_less_le = thm "prefix_less_le";
val set_mono = thm "set_mono";
val Nil_prefix = thm "Nil_prefix";
val prefix_Nil = thm "prefix_Nil";
val Cons_prefix_Cons = thm "Cons_prefix_Cons";
val same_prefix_prefix = thm "same_prefix_prefix";
val append_prefix = thm "append_prefix";
val prefix_appendI = thm "prefix_appendI";
val prefix_Cons = thm "prefix_Cons";
val append_one_prefix = thm "append_one_prefix";
val prefix_length_le = thm "prefix_length_le";
val strict_prefix_length_less = thm "strict_prefix_length_less";
val mono_length = thm "mono_length";
val prefix_iff = thm "prefix_iff";
val prefix_snoc = thm "prefix_snoc";
val prefix_append_iff = thm "prefix_append_iff";
val common_prefix_linear = thm "common_prefix_linear";
val reflexive_Le = thm "reflexive_Le";
val antisym_Le = thm "antisym_Le";
val trans_Le = thm "trans_Le";
val pfixLe_refl = thm "pfixLe_refl";
val pfixLe_trans = thm "pfixLe_trans";
val pfixLe_antisym = thm "pfixLe_antisym";
val prefix_imp_pfixLe = thm "prefix_imp_pfixLe";
val reflexive_Ge = thm "reflexive_Ge";
val antisym_Ge = thm "antisym_Ge";
val trans_Ge = thm "trans_Ge";
val pfixGe_refl = thm "pfixGe_refl";
val pfixGe_trans = thm "pfixGe_trans";
val pfixGe_antisym = thm "pfixGe_antisym";
val prefix_imp_pfixGe = thm "prefix_imp_pfixGe";


(*UNITY*)
val constrains_def = thm "constrains_def";
val stable_def = thm "stable_def";
val invariant_def = thm "invariant_def";
val increasing_def = thm "increasing_def";
val Allowed_def = thm "Allowed_def";
val Id_in_Acts = thm "Id_in_Acts";
val insert_Id_Acts = thm "insert_Id_Acts";
val Id_in_AllowedActs = thm "Id_in_AllowedActs";
val insert_Id_AllowedActs = thm "insert_Id_AllowedActs";
val Init_eq = thm "Init_eq";
val Acts_eq = thm "Acts_eq";
val AllowedActs_eq = thm "AllowedActs_eq";
val surjective_mk_program = thm "surjective_mk_program";
val program_equalityI = thm "program_equalityI";
val program_equalityE = thm "program_equalityE";
val program_equality_iff = thm "program_equality_iff";
val def_prg_Init = thm "def_prg_Init";
val def_prg_Acts = thm "def_prg_Acts";
val def_prg_AllowedActs = thm "def_prg_AllowedActs";
val def_prg_simps = thm "def_prg_simps";
val def_act_simp = thm "def_act_simp";
val def_set_simp = thm "def_set_simp";
val constrainsI = thm "constrainsI";
val constrainsD = thm "constrainsD";
val constrains_empty = thm "constrains_empty";
val constrains_empty2 = thm "constrains_empty2";
val constrains_UNIV = thm "constrains_UNIV";
val constrains_UNIV2 = thm "constrains_UNIV2";
val constrains_weaken_R = thm "constrains_weaken_R";
val constrains_weaken_L = thm "constrains_weaken_L";
val constrains_weaken = thm "constrains_weaken";
val constrains_Un = thm "constrains_Un";
val constrains_UN = thm "constrains_UN";
val constrains_Un_distrib = thm "constrains_Un_distrib";
val constrains_UN_distrib = thm "constrains_UN_distrib";
val constrains_Int_distrib = thm "constrains_Int_distrib";
val constrains_INT_distrib = thm "constrains_INT_distrib";
val constrains_Int = thm "constrains_Int";
val constrains_INT = thm "constrains_INT";
val constrains_imp_subset = thm "constrains_imp_subset";
val constrains_trans = thm "constrains_trans";
val constrains_cancel = thm "constrains_cancel";
val unlessI = thm "unlessI";
val unlessD = thm "unlessD";
val stableI = thm "stableI";
val stableD = thm "stableD";
val stable_UNIV = thm "stable_UNIV";
val stable_Un = thm "stable_Un";
val stable_UN = thm "stable_UN";
val stable_Int = thm "stable_Int";
val stable_INT = thm "stable_INT";
val stable_constrains_Un = thm "stable_constrains_Un";
val stable_constrains_Int = thm "stable_constrains_Int";
val stable_constrains_stable = thm "stable_constrains_stable";
val invariantI = thm "invariantI";
val invariant_Int = thm "invariant_Int";
val increasingD = thm "increasingD";
val increasing_constant = thm "increasing_constant";
val mono_increasing_o = thm "mono_increasing_o";
val strict_increasingD = thm "strict_increasingD";
val elimination = thm "elimination";
val elimination_sing = thm "elimination_sing";
val constrains_strongest_rhs = thm "constrains_strongest_rhs";
val strongest_rhs_is_strongest = thm "strongest_rhs_is_strongest";
val Un_Diff_Diff = thm "Un_Diff_Diff";
val Int_Union_Union = thm "Int_Union_Union";
val Image_less_than = thm "Image_less_than";
val Image_inverse_less_than = thm "Image_inverse_less_than";

(*WFair*)
val stable_transient_empty = thm "stable_transient_empty";
val transient_strengthen = thm "transient_strengthen";
val transientI = thm "transientI";
val transientE = thm "transientE";
val transient_UNIV = thm "transient_UNIV";
val transient_empty = thm "transient_empty";
val ensuresI = thm "ensuresI";
val ensuresD = thm "ensuresD";
val ensures_weaken_R = thm "ensures_weaken_R";
val stable_ensures_Int = thm "stable_ensures_Int";
val stable_transient_ensures = thm "stable_transient_ensures";
val ensures_eq = thm "ensures_eq";
val leadsTo_Basis = thm "leadsTo_Basis";
val leadsTo_Trans = thm "leadsTo_Trans";
val transient_imp_leadsTo = thm "transient_imp_leadsTo";
val leadsTo_Un_duplicate = thm "leadsTo_Un_duplicate";
val leadsTo_Un_duplicate2 = thm "leadsTo_Un_duplicate2";
val leadsTo_Union = thm "leadsTo_Union";
val leadsTo_Union_Int = thm "leadsTo_Union_Int";
val leadsTo_UN = thm "leadsTo_UN";
val leadsTo_Un = thm "leadsTo_Un";
val single_leadsTo_I = thm "single_leadsTo_I";
val leadsTo_induct = thm "leadsTo_induct";
val subset_imp_ensures = thm "subset_imp_ensures";
val subset_imp_leadsTo = thm "subset_imp_leadsTo";
val leadsTo_refl = thm "leadsTo_refl";
val empty_leadsTo = thm "empty_leadsTo";
val leadsTo_UNIV = thm "leadsTo_UNIV";
val leadsTo_induct_pre = thm "leadsTo_induct_pre";
val leadsTo_weaken_R = thm "leadsTo_weaken_R";
val leadsTo_weaken_L = thm "leadsTo_weaken_L";
val leadsTo_Un_distrib = thm "leadsTo_Un_distrib";
val leadsTo_UN_distrib = thm "leadsTo_UN_distrib";
val leadsTo_Union_distrib = thm "leadsTo_Union_distrib";
val leadsTo_weaken = thm "leadsTo_weaken";
val leadsTo_Diff = thm "leadsTo_Diff";
val leadsTo_UN_UN = thm "leadsTo_UN_UN";
val leadsTo_Un_Un = thm "leadsTo_Un_Un";
val leadsTo_cancel2 = thm "leadsTo_cancel2";
val leadsTo_cancel_Diff2 = thm "leadsTo_cancel_Diff2";
val leadsTo_cancel1 = thm "leadsTo_cancel1";
val leadsTo_cancel_Diff1 = thm "leadsTo_cancel_Diff1";
val leadsTo_empty = thm "leadsTo_empty";
val psp_stable = thm "psp_stable";
val psp_stable2 = thm "psp_stable2";
val psp_ensures = thm "psp_ensures";
val psp = thm "psp";
val psp2 = thm "psp2";
val psp_unless = thm "psp_unless";
val leadsTo_wf_induct = thm "leadsTo_wf_induct";
val bounded_induct = thm "bounded_induct";
val lessThan_induct = thm "lessThan_induct";
val lessThan_bounded_induct = thm "lessThan_bounded_induct";
val greaterThan_bounded_induct = thm "greaterThan_bounded_induct";
val wlt_leadsTo = thm "wlt_leadsTo";
val leadsTo_subset = thm "leadsTo_subset";
val leadsTo_eq_subset_wlt = thm "leadsTo_eq_subset_wlt";
val wlt_increasing = thm "wlt_increasing";
val leadsTo_123 = thm "leadsTo_123";
val wlt_constrains_wlt = thm "wlt_constrains_wlt";
val completion = thm "completion";
val finite_completion = thm "finite_completion";
val stable_completion = thm "stable_completion";
val finite_stable_completion = thm "finite_stable_completion";

(*Constrains*)
val Increasing_def = thm "Increasing_def";
val reachable_Init = thm "reachable.Init";
val reachable_Acts = thm "reachable.Acts";
val reachable_equiv_traces = thm "reachable_equiv_traces";
val Init_subset_reachable = thm "Init_subset_reachable";
val stable_reachable = thm "stable_reachable";
val invariant_reachable = thm "invariant_reachable";
val invariant_includes_reachable = thm "invariant_includes_reachable";
val constrains_reachable_Int = thm "constrains_reachable_Int";
val Constrains_eq_constrains = thm "Constrains_eq_constrains";
val constrains_imp_Constrains = thm "constrains_imp_Constrains";
val stable_imp_Stable = thm "stable_imp_Stable";
val ConstrainsI = thm "ConstrainsI";
val Constrains_empty = thm "Constrains_empty";
val Constrains_UNIV = thm "Constrains_UNIV";
val Constrains_weaken_R = thm "Constrains_weaken_R";
val Constrains_weaken_L = thm "Constrains_weaken_L";
val Constrains_weaken = thm "Constrains_weaken";
val Constrains_Un = thm "Constrains_Un";
val Constrains_UN = thm "Constrains_UN";
val Constrains_Int = thm "Constrains_Int";
val Constrains_INT = thm "Constrains_INT";
val Constrains_imp_subset = thm "Constrains_imp_subset";
val Constrains_trans = thm "Constrains_trans";
val Constrains_cancel = thm "Constrains_cancel";
val Stable_eq = thm "Stable_eq";
val Stable_eq_stable = thm "Stable_eq_stable";
val StableI = thm "StableI";
val StableD = thm "StableD";
val Stable_Un = thm "Stable_Un";
val Stable_Int = thm "Stable_Int";
val Stable_Constrains_Un = thm "Stable_Constrains_Un";
val Stable_Constrains_Int = thm "Stable_Constrains_Int";
val Stable_UN = thm "Stable_UN";
val Stable_INT = thm "Stable_INT";
val Stable_reachable = thm "Stable_reachable";
val IncreasingD = thm "IncreasingD";
val mono_Increasing_o = thm "mono_Increasing_o";
val strict_IncreasingD = thm "strict_IncreasingD";
val increasing_imp_Increasing = thm "increasing_imp_Increasing";
val Increasing_constant = thm "Increasing_constant";
val Elimination = thm "Elimination";
val Elimination_sing = thm "Elimination_sing";
val AlwaysI = thm "AlwaysI";
val AlwaysD = thm "AlwaysD";
val AlwaysE = thm "AlwaysE";
val Always_imp_Stable = thm "Always_imp_Stable";
val Always_includes_reachable = thm "Always_includes_reachable";
val invariant_imp_Always = thm "invariant_imp_Always";
val Always_reachable = thm "Always_reachable";
val Always_eq_invariant_reachable = thm "Always_eq_invariant_reachable";
val Always_eq_includes_reachable = thm "Always_eq_includes_reachable";
val Always_UNIV_eq = thm "Always_UNIV_eq";
val UNIV_AlwaysI = thm "UNIV_AlwaysI";
val Always_eq_UN_invariant = thm "Always_eq_UN_invariant";
val Always_weaken = thm "Always_weaken";
val Always_Constrains_pre = thm "Always_Constrains_pre";
val Always_Constrains_post = thm "Always_Constrains_post";
val Always_ConstrainsI = thm "Always_ConstrainsI";
val Always_ConstrainsD = thm "Always_ConstrainsD";
val Always_Constrains_weaken = thm "Always_Constrains_weaken";
val Always_Int_distrib = thm "Always_Int_distrib";
val Always_INT_distrib = thm "Always_INT_distrib";
val Always_Int_I = thm "Always_Int_I";
val Always_Compl_Un_eq = thm "Always_Compl_Un_eq";
val Always_thin = thm "Always_thin";

(*FP*)
val stable_FP_Orig_Int = thm "stable_FP_Orig_Int";
val FP_Orig_weakest = thm "FP_Orig_weakest";
val stable_FP_Int = thm "stable_FP_Int";
val FP_equivalence = thm "FP_equivalence";
val FP_weakest = thm "FP_weakest";
val Compl_FP = thm "Compl_FP";
val Diff_FP = thm "Diff_FP";

(*SubstAx*)
val LeadsTo_eq_leadsTo = thm "LeadsTo_eq_leadsTo";
val Always_LeadsTo_pre = thm "Always_LeadsTo_pre";
val Always_LeadsTo_post = thm "Always_LeadsTo_post";
val Always_LeadsToI = thm "Always_LeadsToI";
val Always_LeadsToD = thm "Always_LeadsToD";
val leadsTo_imp_LeadsTo = thm "leadsTo_imp_LeadsTo";
val LeadsTo_Trans = thm "LeadsTo_Trans";
val LeadsTo_Union = thm "LeadsTo_Union";
val LeadsTo_UNIV = thm "LeadsTo_UNIV";
val LeadsTo_Un_duplicate = thm "LeadsTo_Un_duplicate";
val LeadsTo_Un_duplicate2 = thm "LeadsTo_Un_duplicate2";
val LeadsTo_UN = thm "LeadsTo_UN";
val LeadsTo_Un = thm "LeadsTo_Un";
val single_LeadsTo_I = thm "single_LeadsTo_I";
val subset_imp_LeadsTo = thm "subset_imp_LeadsTo";
val empty_LeadsTo = thm "empty_LeadsTo";
val LeadsTo_weaken_R = thm "LeadsTo_weaken_R";
val LeadsTo_weaken_L = thm "LeadsTo_weaken_L";
val LeadsTo_weaken = thm "LeadsTo_weaken";
val Always_LeadsTo_weaken = thm "Always_LeadsTo_weaken";
val LeadsTo_Un_post = thm "LeadsTo_Un_post";
val LeadsTo_Trans_Un = thm "LeadsTo_Trans_Un";
val LeadsTo_Un_distrib = thm "LeadsTo_Un_distrib";
val LeadsTo_UN_distrib = thm "LeadsTo_UN_distrib";
val LeadsTo_Union_distrib = thm "LeadsTo_Union_distrib";
val LeadsTo_Basis = thm "LeadsTo_Basis";
val EnsuresI = thm "EnsuresI";
val Always_LeadsTo_Basis = thm "Always_LeadsTo_Basis";
val LeadsTo_Diff = thm "LeadsTo_Diff";
val LeadsTo_UN_UN = thm "LeadsTo_UN_UN";
val LeadsTo_UN_UN_noindex = thm "LeadsTo_UN_UN_noindex";
val all_LeadsTo_UN_UN = thm "all_LeadsTo_UN_UN";
val LeadsTo_Un_Un = thm "LeadsTo_Un_Un";
val LeadsTo_cancel2 = thm "LeadsTo_cancel2";
val LeadsTo_cancel_Diff2 = thm "LeadsTo_cancel_Diff2";
val LeadsTo_cancel1 = thm "LeadsTo_cancel1";
val LeadsTo_cancel_Diff1 = thm "LeadsTo_cancel_Diff1";
val LeadsTo_empty = thm "LeadsTo_empty";
val PSP_Stable = thm "PSP_Stable";
val PSP_Stable2 = thm "PSP_Stable2";
val PSP = thm "PSP";
val PSP2 = thm "PSP2";
val PSP_Unless = thm "PSP_Unless";
val Stable_transient_Always_LeadsTo = thm "Stable_transient_Always_LeadsTo";
val LeadsTo_wf_induct = thm "LeadsTo_wf_induct";
val Bounded_induct = thm "Bounded_induct";
val LessThan_induct = thm "LessThan_induct";
val integ_0_le_induct = thm "integ_0_le_induct";
val LessThan_bounded_induct = thm "LessThan_bounded_induct";
val GreaterThan_bounded_induct = thm "GreaterThan_bounded_induct";
val Completion = thm "Completion";
val Finite_completion = thm "Finite_completion";
val Stable_completion = thm "Stable_completion";
val Finite_stable_completion = thm "Finite_stable_completion";

(*Union*)
val Init_SKIP = thm "Init_SKIP";
val Acts_SKIP = thm "Acts_SKIP";
val AllowedActs_SKIP = thm "AllowedActs_SKIP";
val reachable_SKIP = thm "reachable_SKIP";
val SKIP_in_constrains_iff = thm "SKIP_in_constrains_iff";
val SKIP_in_Constrains_iff = thm "SKIP_in_Constrains_iff";
val SKIP_in_stable = thm "SKIP_in_stable";
val Init_Join = thm "Init_Join";
val Acts_Join = thm "Acts_Join";
val AllowedActs_Join = thm "AllowedActs_Join";
val JN_empty = thm "JN_empty";
val JN_insert = thm "JN_insert";
val Init_JN = thm "Init_JN";
val Acts_JN = thm "Acts_JN";
val AllowedActs_JN = thm "AllowedActs_JN";
val JN_cong = thm "JN_cong";
val Join_commute = thm "Join_commute";
val Join_assoc = thm "Join_assoc";
val Join_left_commute = thm "Join_left_commute";
val Join_SKIP_left = thm "Join_SKIP_left";
val Join_SKIP_right = thm "Join_SKIP_right";
val Join_absorb = thm "Join_absorb";
val Join_left_absorb = thm "Join_left_absorb";
val Join_ac = thms "Join_ac";
val JN_absorb = thm "JN_absorb";
val JN_Un = thm "JN_Un";
val JN_constant = thm "JN_constant";
val JN_Join_distrib = thm "JN_Join_distrib";
val JN_Join_miniscope = thm "JN_Join_miniscope";
val JN_Join_diff = thm "JN_Join_diff";
val JN_constrains = thm "JN_constrains";
val Join_constrains = thm "Join_constrains";
val Join_unless = thm "Join_unless";
val Join_constrains_weaken = thm "Join_constrains_weaken";
val JN_constrains_weaken = thm "JN_constrains_weaken";
val JN_stable = thm "JN_stable";
val invariant_JN_I = thm "invariant_JN_I";
val Join_stable = thm "Join_stable";
val Join_increasing = thm "Join_increasing";
val invariant_JoinI = thm "invariant_JoinI";
val FP_JN = thm "FP_JN";
val JN_transient = thm "JN_transient";
val Join_transient = thm "Join_transient";
val Join_transient_I1 = thm "Join_transient_I1";
val Join_transient_I2 = thm "Join_transient_I2";
val JN_ensures = thm "JN_ensures";
val Join_ensures = thm "Join_ensures";
val stable_Join_constrains = thm "stable_Join_constrains";
val stable_Join_Always1 = thm "stable_Join_Always1";
val stable_Join_Always2 = thm "stable_Join_Always2";
val stable_Join_ensures1 = thm "stable_Join_ensures1";
val stable_Join_ensures2 = thm "stable_Join_ensures2";
val ok_SKIP1 = thm "ok_SKIP1";
val ok_SKIP2 = thm "ok_SKIP2";
val ok_Join_commute = thm "ok_Join_commute";
val ok_commute = thm "ok_commute";
val ok_sym = thm "ok_sym";
val ok_iff_OK = thm "ok_iff_OK";
val ok_Join_iff1 = thm "ok_Join_iff1";
val ok_Join_iff2 = thm "ok_Join_iff2";
val ok_Join_commute_I = thm "ok_Join_commute_I";
val ok_JN_iff1 = thm "ok_JN_iff1";
val ok_JN_iff2 = thm "ok_JN_iff2";
val OK_iff_ok = thm "OK_iff_ok";
val OK_imp_ok = thm "OK_imp_ok";
val Allowed_SKIP = thm "Allowed_SKIP";
val Allowed_Join = thm "Allowed_Join";
val Allowed_JN = thm "Allowed_JN";
val ok_iff_Allowed = thm "ok_iff_Allowed";
val OK_iff_Allowed = thm "OK_iff_Allowed";
val safety_prop_Acts_iff = thm "safety_prop_Acts_iff";
val safety_prop_AllowedActs_iff_Allowed = thm "safety_prop_AllowedActs_iff_Allowed";
val Allowed_eq = thm "Allowed_eq";
val def_prg_Allowed = thm "def_prg_Allowed";
val safety_prop_constrains = thm "safety_prop_constrains";
val safety_prop_stable = thm "safety_prop_stable";
val safety_prop_Int = thm "safety_prop_Int";
val safety_prop_INTER1 = thm "safety_prop_INTER1";
val safety_prop_INTER = thm "safety_prop_INTER";
val def_UNION_ok_iff = thm "def_UNION_ok_iff";

(*Comp*)
val preserves_def = thm "preserves_def";
val funPair_def = thm "funPair_def";
val componentI = thm "componentI";
val component_eq_subset = thm "component_eq_subset";
val component_SKIP = thm "component_SKIP";
val component_refl = thm "component_refl";
val SKIP_minimal = thm "SKIP_minimal";
val component_Join1 = thm "component_Join1";
val component_Join2 = thm "component_Join2";
val Join_absorb1 = thm "Join_absorb1";
val Join_absorb2 = thm "Join_absorb2";
val JN_component_iff = thm "JN_component_iff";
val component_JN = thm "component_JN";
val component_trans = thm "component_trans";
val component_antisym = thm "component_antisym";
val Join_component_iff = thm "Join_component_iff";
val component_constrains = thm "component_constrains";
val program_less_le = thm "program_less_le";
val preservesI = thm "preservesI";
val preserves_imp_eq = thm "preserves_imp_eq";
val Join_preserves = thm "Join_preserves";
val JN_preserves = thm "JN_preserves";
val SKIP_preserves = thm "SKIP_preserves";
val funPair_apply = thm "funPair_apply";
val preserves_funPair = thm "preserves_funPair";
val funPair_o_distrib = thm "funPair_o_distrib";
val fst_o_funPair = thm "fst_o_funPair";
val snd_o_funPair = thm "snd_o_funPair";
val subset_preserves_o = thm "subset_preserves_o";
val preserves_subset_stable = thm "preserves_subset_stable";
val preserves_subset_increasing = thm "preserves_subset_increasing";
val preserves_id_subset_stable = thm "preserves_id_subset_stable";
val safety_prop_preserves = thm "safety_prop_preserves";
val stable_localTo_stable2 = thm "stable_localTo_stable2";
val Increasing_preserves_Stable = thm "Increasing_preserves_Stable";
val component_of_imp_component = thm "component_of_imp_component";
val component_of_refl = thm "component_of_refl";
val component_of_SKIP = thm "component_of_SKIP";
val component_of_trans = thm "component_of_trans";
val strict_component_of_eq = thm "strict_component_of_eq";
val localize_Init_eq = thm "localize_Init_eq";
val localize_Acts_eq = thm "localize_Acts_eq";
val localize_AllowedActs_eq = thm "localize_AllowedActs_eq";

(*Guar*)
val guar_def = thm "guar_def";
val OK_insert_iff = thm "OK_insert_iff";
val ex1 = thm "ex1";
val ex2 = thm "ex2";
val ex_prop_finite = thm "ex_prop_finite";
val ex_prop_equiv = thm "ex_prop_equiv";
val uv1 = thm "uv1";
val uv2 = thm "uv2";
val uv_prop_finite = thm "uv_prop_finite";
val guaranteesI = thm "guaranteesI";
val guaranteesD = thm "guaranteesD";
val component_guaranteesD = thm "component_guaranteesD";
val guarantees_weaken = thm "guarantees_weaken";
val subset_imp_guarantees_UNIV = thm "subset_imp_guarantees_UNIV";
val subset_imp_guarantees = thm "subset_imp_guarantees";
val ex_prop_imp = thm "ex_prop_imp";
val guarantees_imp = thm "guarantees_imp";
val ex_prop_equiv2 = thm "ex_prop_equiv2";
val guarantees_UN_left = thm "guarantees_UN_left";
val guarantees_Un_left = thm "guarantees_Un_left";
val guarantees_INT_right = thm "guarantees_INT_right";
val guarantees_Int_right = thm "guarantees_Int_right";
val guarantees_Int_right_I = thm "guarantees_Int_right_I";
val guarantees_INT_right_iff = thm "guarantees_INT_right_iff";
val shunting = thm "shunting";
val contrapositive = thm "contrapositive";
val combining1 = thm "combining1";
val combining2 = thm "combining2";
val all_guarantees = thm "all_guarantees";
val ex_guarantees = thm "ex_guarantees";
val guarantees_Join_Int = thm "guarantees_Join_Int";
val guarantees_Join_Un = thm "guarantees_Join_Un";
val guarantees_JN_INT = thm "guarantees_JN_INT";
val guarantees_JN_UN = thm "guarantees_JN_UN";
val guarantees_Join_I1 = thm "guarantees_Join_I1";
val guarantees_Join_I2 = thm "guarantees_Join_I2";
val guarantees_JN_I = thm "guarantees_JN_I";
val Join_welldef_D1 = thm "Join_welldef_D1";
val Join_welldef_D2 = thm "Join_welldef_D2";
val refines_refl = thm "refines_refl";
val ex_refinement_thm = thm "ex_refinement_thm";
val uv_refinement_thm = thm "uv_refinement_thm";
val guarantees_equiv = thm "guarantees_equiv";
val wg_weakest = thm "wg_weakest";
val wg_guarantees = thm "wg_guarantees";
val wg_equiv = thm "wg_equiv";
val component_of_wg = thm "component_of_wg";
val wg_finite = thm "wg_finite";
val wg_ex_prop = thm "wg_ex_prop";
val wx_subset = thm "wx_subset";
val wx_ex_prop = thm "wx_ex_prop";
val wx_weakest = thm "wx_weakest";
val wx'_ex_prop = thm "wx'_ex_prop";
val wx_equiv = thm "wx_equiv";
val guarantees_wx_eq = thm "guarantees_wx_eq";
val stable_guarantees_Always = thm "stable_guarantees_Always";
val leadsTo_Basis = thm "leadsTo_Basis";
val constrains_guarantees_leadsTo = thm "constrains_guarantees_leadsTo";

(*Extend*)
val Restrict_iff = thm "Restrict_iff";
val Restrict_UNIV = thm "Restrict_UNIV";
val Restrict_empty = thm "Restrict_empty";
val Restrict_Int = thm "Restrict_Int";
val Restrict_triv = thm "Restrict_triv";
val Restrict_subset = thm "Restrict_subset";
val Restrict_eq_mono = thm "Restrict_eq_mono";
val Restrict_imageI = thm "Restrict_imageI";
val Domain_Restrict = thm "Domain_Restrict";
val Image_Restrict = thm "Image_Restrict";
val insert_Id_image_Acts = thm "insert_Id_image_Acts";
val good_mapI = thm "good_mapI";
val good_map_is_surj = thm "good_map_is_surj";
val fst_inv_equalityI = thm "fst_inv_equalityI";
val project_set_iff = thm "project_set_iff";
val extend_set_mono = thm "extend_set_mono";
val extend_set_empty = thm "extend_set_empty";
val project_set_Int_subset = thm "project_set_Int_subset";
val Init_extend = thm "Init_extend";
val Init_project = thm "Init_project";
val Acts_project = thm "Acts_project";
val project_set_UNIV = thm "project_set_UNIV";
val project_set_Union = thm "project_set_Union";
val project_act_mono = thm "project_act_mono";
val project_constrains_project_set = thm "project_constrains_project_set";
val project_stable_project_set = thm "project_stable_project_set";


(*Rename*)
val good_map_bij = thm "good_map_bij";
val fst_o_inv_eq_inv = thm "fst_o_inv_eq_inv";
val mem_rename_set_iff = thm "mem_rename_set_iff";
val extend_set_eq_image = thm "extend_set_eq_image";
val Init_rename = thm "Init_rename";
val extend_set_inv = thm "extend_set_inv";
val bij_extend_act_eq_project_act = thm "bij_extend_act_eq_project_act";
val bij_extend_act = thm "bij_extend_act";
val bij_project_act = thm "bij_project_act";
val bij_inv_project_act_eq = thm "bij_inv_project_act_eq";
val Acts_project = thm "Acts_project";
val extend_inv = thm "extend_inv";
val rename_inv_rename = thm "rename_inv_rename";
val rename_rename_inv = thm "rename_rename_inv";
val rename_inv_eq = thm "rename_inv_eq";
val bij_extend = thm "bij_extend";
val bij_project = thm "bij_project";
val inv_project_eq = thm "inv_project_eq";
val Allowed_rename = thm "Allowed_rename";
val bij_rename = thm "bij_rename";
val surj_rename = thm "surj_rename";
val inj_rename_imp_inj = thm "inj_rename_imp_inj";
val surj_rename_imp_surj = thm "surj_rename_imp_surj";
val bij_rename_imp_bij = thm "bij_rename_imp_bij";
val bij_rename_iff = thm "bij_rename_iff";
val rename_SKIP = thm "rename_SKIP";
val rename_Join = thm "rename_Join";
val rename_JN = thm "rename_JN";
val rename_constrains = thm "rename_constrains";
val rename_stable = thm "rename_stable";
val rename_invariant = thm "rename_invariant";
val rename_increasing = thm "rename_increasing";
val reachable_rename_eq = thm "reachable_rename_eq";
val rename_Constrains = thm "rename_Constrains";
val rename_Stable = thm "rename_Stable";
val rename_Always = thm "rename_Always";
val rename_Increasing = thm "rename_Increasing";
val rename_transient = thm "rename_transient";
val rename_ensures = thm "rename_ensures";
val rename_leadsTo = thm "rename_leadsTo";
val rename_LeadsTo = thm "rename_LeadsTo";
val rename_rename_guarantees_eq = thm "rename_rename_guarantees_eq";
val rename_guarantees_eq_rename_inv = thm "rename_guarantees_eq_rename_inv";
val rename_preserves = thm "rename_preserves";
val ok_rename_iff = thm "ok_rename_iff";
val OK_rename_iff = thm "OK_rename_iff";
val bij_eq_rename = thm "bij_eq_rename";
val rename_image_constrains = thm "rename_image_constrains";
val rename_image_stable = thm "rename_image_stable";
val rename_image_increasing = thm "rename_image_increasing";
val rename_image_invariant = thm "rename_image_invariant";
val rename_image_Constrains = thm "rename_image_Constrains";
val rename_image_preserves = thm "rename_image_preserves";
val rename_image_Stable = thm "rename_image_Stable";
val rename_image_Increasing = thm "rename_image_Increasing";
val rename_image_Always = thm "rename_image_Always";
val rename_image_leadsTo = thm "rename_image_leadsTo";
val rename_image_LeadsTo = thm "rename_image_LeadsTo";



(*Lift_prog*)
val sub_def = thm "sub_def";
val lift_map_def = thm "lift_map_def";
val drop_map_def = thm "drop_map_def";
val insert_map_inverse = thm "insert_map_inverse";
val insert_map_delete_map_eq = thm "insert_map_delete_map_eq";
val insert_map_inject1 = thm "insert_map_inject1";
val insert_map_inject2 = thm "insert_map_inject2";
val insert_map_inject = thm "insert_map_inject";
val insert_map_inject = thm "insert_map_inject";
val lift_map_eq_iff = thm "lift_map_eq_iff";
val drop_map_lift_map_eq = thm "drop_map_lift_map_eq";
val inj_lift_map = thm "inj_lift_map";
val lift_map_drop_map_eq = thm "lift_map_drop_map_eq";
val drop_map_inject = thm "drop_map_inject";
val surj_lift_map = thm "surj_lift_map";
val bij_lift_map = thm "bij_lift_map";
val inv_lift_map_eq = thm "inv_lift_map_eq";
val inv_drop_map_eq = thm "inv_drop_map_eq";
val bij_drop_map = thm "bij_drop_map";
val sub_apply = thm "sub_apply";
val lift_set_empty = thm "lift_set_empty";
val lift_set_iff = thm "lift_set_iff";
val lift_set_iff2 = thm "lift_set_iff2";
val lift_set_mono = thm "lift_set_mono";
val lift_set_Un_distrib = thm "lift_set_Un_distrib";
val lift_set_Diff_distrib = thm "lift_set_Diff_distrib";
val bij_lift = thm "bij_lift";
val lift_SKIP = thm "lift_SKIP";
val lift_Join = thm "lift_Join";
val lift_JN = thm "lift_JN";
val lift_constrains = thm "lift_constrains";
val lift_stable = thm "lift_stable";
val lift_invariant = thm "lift_invariant";
val lift_Constrains = thm "lift_Constrains";
val lift_Stable = thm "lift_Stable";
val lift_Always = thm "lift_Always";
val lift_transient = thm "lift_transient";
val lift_ensures = thm "lift_ensures";
val lift_leadsTo = thm "lift_leadsTo";
val lift_LeadsTo = thm "lift_LeadsTo";
val lift_lift_guarantees_eq = thm "lift_lift_guarantees_eq";
val lift_guarantees_eq_lift_inv = thm "lift_guarantees_eq_lift_inv";
val lift_preserves_snd_I = thm "lift_preserves_snd_I";
val delete_map_eqE = thm "delete_map_eqE";
val delete_map_eqE = thm "delete_map_eqE";
val delete_map_neq_apply = thm "delete_map_neq_apply";
val vimage_o_fst_eq = thm "vimage_o_fst_eq";
val vimage_sub_eq_lift_set = thm "vimage_sub_eq_lift_set";
val mem_lift_act_iff = thm "mem_lift_act_iff";
val preserves_snd_lift_stable = thm "preserves_snd_lift_stable";
val constrains_imp_lift_constrains = thm "constrains_imp_lift_constrains";
val insert_map_upd_same = thm "insert_map_upd_same";
val insert_map_upd = thm "insert_map_upd";
val insert_map_eq_diff = thm "insert_map_eq_diff";
val lift_map_eq_diff = thm "lift_map_eq_diff";
val lift_transient_eq_disj = thm "lift_transient_eq_disj";
val lift_map_image_Times = thm "lift_map_image_Times";
val lift_preserves_eq = thm "lift_preserves_eq";
val lift_preserves_sub = thm "lift_preserves_sub";
val o_equiv_assoc = thm "o_equiv_assoc";
val o_equiv_apply = thm "o_equiv_apply";
val fst_o_lift_map = thm "fst_o_lift_map";
val snd_o_lift_map = thm "snd_o_lift_map";
val extend_act_extend_act = thm "extend_act_extend_act";
val project_act_project_act = thm "project_act_project_act";
val project_act_extend_act = thm "project_act_extend_act";
val act_in_UNION_preserves_fst = thm "act_in_UNION_preserves_fst";
val UNION_OK_lift_I = thm "UNION_OK_lift_I";
val OK_lift_I = thm "OK_lift_I";
val Allowed_lift = thm "Allowed_lift";
val lift_image_preserves = thm "lift_image_preserves";


(*PPROD*)
val Init_PLam = thm "Init_PLam";
val PLam_empty = thm "PLam_empty";
val PLam_SKIP = thm "PLam_SKIP";
val PLam_insert = thm "PLam_insert";
val PLam_component_iff = thm "PLam_component_iff";
val component_PLam = thm "component_PLam";
val PLam_constrains = thm "PLam_constrains";
val PLam_stable = thm "PLam_stable";
val PLam_transient = thm "PLam_transient";
val PLam_ensures = thm "PLam_ensures";
val PLam_leadsTo_Basis = thm "PLam_leadsTo_Basis";
val invariant_imp_PLam_invariant = thm "invariant_imp_PLam_invariant";
val PLam_preserves_fst = thm "PLam_preserves_fst";
val PLam_preserves_snd = thm "PLam_preserves_snd";
val guarantees_PLam_I = thm "guarantees_PLam_I";
val Allowed_PLam = thm "Allowed_PLam";
val PLam_preserves = thm "PLam_preserves";

(*Follows*)
val mono_Always_o = thm "mono_Always_o";
val mono_LeadsTo_o = thm "mono_LeadsTo_o";
val Follows_constant = thm "Follows_constant";
val mono_Follows_o = thm "mono_Follows_o";
val mono_Follows_apply = thm "mono_Follows_apply";
val Follows_trans = thm "Follows_trans";
val Follows_Increasing1 = thm "Follows_Increasing1";
val Follows_Increasing2 = thm "Follows_Increasing2";
val Follows_Bounded = thm "Follows_Bounded";
val Follows_LeadsTo = thm "Follows_LeadsTo";
val Follows_LeadsTo_pfixLe = thm "Follows_LeadsTo_pfixLe";
val Follows_LeadsTo_pfixGe = thm "Follows_LeadsTo_pfixGe";
val Always_Follows1 = thm "Always_Follows1";
val Always_Follows2 = thm "Always_Follows2";
val increasing_Un = thm "increasing_Un";
val Increasing_Un = thm "Increasing_Un";
val Always_Un = thm "Always_Un";
val Follows_Un = thm "Follows_Un";
val increasing_union = thm "increasing_union";
val Increasing_union = thm "Increasing_union";
val Always_union = thm "Always_union";
val Follows_union = thm "Follows_union";
val Follows_setsum = thm "Follows_setsum";
val Increasing_imp_Stable_pfixGe = thm "Increasing_imp_Stable_pfixGe";
val LeadsTo_le_imp_pfixGe = thm "LeadsTo_le_imp_pfixGe";


(*Lazy unfolding of actions or of sets*)
fun simp_of_act def = def RS def_act_simp;

fun simp_of_set def = def RS def_set_simp;


(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val Always_Int_tac = dtac Always_Int_I THEN' assume_tac THEN' etac Always_thin

(*Combines a list of invariance THEOREMS into one.*)
val Always_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Always_Int_I)

(*proves "co" properties when the program is specified*)
fun gen_constrains_tac(cs,ss) i = 
   SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
	      REPEAT (etac Always_ConstrainsI 1
		      ORELSE
		      resolve_tac [StableI, stableI,
				   constrains_imp_Constrains] 1),
	      rtac constrainsI 1,
	      full_simp_tac ss 1,
	      REPEAT (FIRSTGOAL (etac disjE)),
	      ALLGOALS (clarify_tac cs),
	      ALLGOALS (asm_lr_simp_tac ss)]) i;

(*proves "ensures/leadsTo" properties when the program is specified*)
fun gen_ensures_tac(cs,ss) sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
	      etac Always_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [LeadsTo_Basis, leadsTo_Basis,
				    EnsuresI, ensuresI] 1),
	      (*now there are two subgoals: co & transient*)
	      simp_tac ss 2,
	      res_inst_tac [("act", sact)] transientI 2,
                 (*simplify the command's domain*)
	      simp_tac (ss addsimps [Domain_def]) 3,
	      gen_constrains_tac (cs,ss) 1,
	      ALLGOALS (clarify_tac cs),
	      ALLGOALS (asm_lr_simp_tac ss)]);

fun constrains_tac st = gen_constrains_tac (claset(), simpset()) st;

fun ensures_tac sact = gen_ensures_tac (claset(), simpset()) sact;


(*Composition equivalences, from Lift_prog*)

fun make_o_equivs th =
    [th,
     th RS o_equiv_assoc |> simplify (HOL_ss addsimps [o_assoc]),
     th RS o_equiv_apply |> simplify (HOL_ss addsimps [o_def, sub_def])];

Addsimps (make_o_equivs fst_o_funPair @ make_o_equivs snd_o_funPair);

Addsimps (make_o_equivs fst_o_lift_map @ make_o_equivs snd_o_lift_map);
