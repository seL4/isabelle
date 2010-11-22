theory Hotel_Example_Small_Generator
imports Hotel_Example Predicate_Compile_Alternative_Defs
uses "~~/src/HOL/Tools/Predicate_Compile/predicate_compile_quickcheck.ML"
begin

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

setup {* Context.theory_map (Quickcheck.add_generator ("small_generators_depth_14", Predicate_Compile_Quickcheck.quickcheck_compile_term
  Predicate_Compile_Aux.Pos_Generator_DSeq true true 14)) *}


setup {* Context.theory_map (Quickcheck.add_generator ("small_generators_depth_15", Predicate_Compile_Quickcheck.quickcheck_compile_term
  Predicate_Compile_Aux.Pos_Generator_DSeq true true 15)) *}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = small_generators_depth_14, finite_types = false, iterations = 1, size = 1, timeout = 60.0, expect = no_counterexample]
quickcheck[generator = small_generators_depth_15, finite_types = false, iterations = 1, size = 1, timeout = 60.0, expect = counterexample]
oops


end