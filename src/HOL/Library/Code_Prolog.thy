(*  Title:      HOL/Library/Code_Prolog.thy
    Author:     Lukas Bulwahn, TUM 2010
*)

header {* Code generation of prolog programs *}

theory Code_Prolog
imports Main
uses "~~/src/HOL/Tools/Predicate_Compile/code_prolog.ML"
begin

section {* Setup for Numerals *}

setup {* Predicate_Compile_Data.ignore_consts
  [@{const_name numeral}, @{const_name neg_numeral}] *}

setup {* Predicate_Compile_Data.keep_functions
  [@{const_name numeral}, @{const_name neg_numeral}] *}

end
