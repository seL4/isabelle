theory Hotel_Example_Small_Generator
imports Hotel_Example "~~/src/HOL/Library/Predicate_Compile_Alternative_Defs"
begin

ML_file "~~/src/HOL/Tools/Predicate_Compile/predicate_compile_quickcheck.ML"

declare Let_def[code_pred_inline]

lemma [code_pred_inline]: "insert == (%y A x. y = x | A x)"
by (auto simp add: insert_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)

lemma [code_pred_inline]: "(op -) == (%A B x. A x \<and> \<not> B x)"
by (auto simp add: Diff_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)

instantiation room :: small_lazy
begin

definition
  "small_lazy i = Lazy_Sequence.single Room0"

instance ..

end

instantiation key :: small_lazy
begin

definition
  "small_lazy i = Lazy_Sequence.append (Lazy_Sequence.single Key0) (Lazy_Sequence.append (Lazy_Sequence.single Key1) (Lazy_Sequence.append (Lazy_Sequence.single Key2) (Lazy_Sequence.single Key3)))"

instance ..

end

instantiation guest :: small_lazy
begin

definition
  "small_lazy i = Lazy_Sequence.append (Lazy_Sequence.single Guest0) (Lazy_Sequence.single Guest1)"

instance ..

end

ML {* 
val small_15_active = Attrib.setup_config_bool @{binding quickcheck_small_14_active} (K false);
val small_14_active = Attrib.setup_config_bool @{binding quickcheck_small_15_active} (K false);
*}

setup {*
  Context.theory_map (Quickcheck.add_tester ("small_generators_depth_14",
    (small_14_active, Predicate_Compile_Quickcheck.test_goals
      (Predicate_Compile_Aux.Pos_Generator_DSeq, true, true, 14))))
  #> Context.theory_map (Quickcheck.add_tester ("small_generators_depth_15",
    (small_15_active, Predicate_Compile_Quickcheck.test_goals
      (Predicate_Compile_Aux.Pos_Generator_DSeq, true, true, 15))))
*}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
(*quickcheck[tester = small_generators_depth_14, finite_types = false, iterations = 1, size = 1, timeout = 1200.0, expect = no_counterexample]*)
quickcheck[tester = small_generators_depth_15, finite_types = false, iterations = 1, size = 1, timeout = 2400.0, expect = counterexample]
oops


end