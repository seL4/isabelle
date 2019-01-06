(*  Title:      HOL/Library/Code_Prolog.thy
    Author:     Lukas Bulwahn, TUM 2010
*)

section \<open>Code generation of prolog programs\<close>

theory Code_Prolog
imports Main
keywords "values_prolog" :: diag
begin

ML_file \<open>~~/src/HOL/Tools/Predicate_Compile/code_prolog.ML\<close>

section \<open>Setup for Numerals\<close>

setup \<open>Predicate_Compile_Data.ignore_consts [\<^const_name>\<open>numeral\<close>]\<close>

setup \<open>Predicate_Compile_Data.keep_functions [\<^const_name>\<open>numeral\<close>]\<close>

end
