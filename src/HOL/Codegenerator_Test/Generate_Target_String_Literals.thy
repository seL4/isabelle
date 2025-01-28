(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Test of target-language string literal operations\<close>

theory Generate_Target_String_Literals
imports
  "HOL-Library.Code_Test"
begin

context
begin

qualified definition computations where
  \<open>computations = (
    STR ''abc'' + STR 0x20 + STR ''def'',
    String.implode ''abc'',
    String.explode STR ''abc'',
    String.literal_of_asciis [10, 20, 30, 40, 1111, 2222, 3333],
    size (STR ''abc''),
    STR ''def'' \<le> STR ''abc'',
    STR ''abc'' < STR ''def''
  )\<close>

qualified definition results where
  \<open>results = (
    STR ''abc def'',
    STR ''abc'',
    ''abc'',
    STR ''\<newline>'' + STR 0x14 + STR 0x1E + STR ''(W.'' + STR 0x05,
    3,
    False,
    True
  )\<close>

qualified definition check where
  \<open>check \<longleftrightarrow> computations = results\<close>

lemma check
  by code_simp

lemma check
  by normalization

lemma check
  by eval

test_code check in Scala

end

end
