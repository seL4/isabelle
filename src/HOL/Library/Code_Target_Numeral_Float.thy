(*  Title:      HOL/Library/Code_Target_Numeral_Float.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Preprocessor setup for floats implemented by target language numerals\<close>

theory Code_Target_Numeral_Float
imports Float Code_Target_Numeral
begin

lemma numeral_float_computation_unfold [code_computation_unfold]:
  \<open>numeral k = Float (int_of_integer (Code_Numeral.positive k)) 0\<close>
  \<open>- numeral k = Float (int_of_integer (Code_Numeral.negative k)) 0\<close>
  by (simp_all add: Float.compute_float_numeral Float.compute_float_neg_numeral)

end
