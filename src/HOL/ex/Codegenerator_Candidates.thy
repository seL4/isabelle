
(* Author: Florian Haftmann, TU Muenchen *)

header {* A huge collection of equations to generate code from *}

theory Codegenerator_Candidates
imports
  Complex_Main
  AssocList
  Binomial
  Commutative_Ring
  Enum
  List_Prefix
  Nat_Infinity
  Nested_Environment
  Option_ord
  Permutation
  Primes
  Product_ord
  SetsAndFunctions
  Tree
  While_Combinator
  Word
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/ex/Records"
begin

(*temporary Haskell workaround*)
declare typerep_fun_def [code inline]
declare typerep_prod_def [code inline]
declare typerep_sum_def [code inline]
declare typerep_cpoint_ext_type_def [code inline]
declare typerep_itself_def [code inline]
declare typerep_list_def [code inline]
declare typerep_option_def [code inline]
declare typerep_point_ext_type_def [code inline]
declare typerep_point'_ext_type_def [code inline]
declare typerep_point''_ext_type_def [code inline]
declare typerep_pol_def [code inline]
declare typerep_polex_def [code inline]

(*avoid popular infixes*)
code_reserved SML union inter upto

end
