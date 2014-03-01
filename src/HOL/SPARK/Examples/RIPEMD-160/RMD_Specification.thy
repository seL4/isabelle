(*  Title:      HOL/SPARK/Examples/RIPEMD-160/RMD_Specification.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory RMD_Specification
imports RMD "~~/src/HOL/SPARK/SPARK"
begin

(* bit operations *)

abbreviation rotate_left :: "int \<Rightarrow> int \<Rightarrow> int" where
  "rotate_left i w == uint (word_rotl (nat i) (word_of_int w::word32))"

spark_proof_functions
  wordops__rotate_left = rotate_left


(* Conversions for proof functions *)
abbreviation k_l_spec :: " int => int " where
  "k_l_spec j == uint (K (nat j))"
abbreviation k_r_spec :: " int => int " where
  "k_r_spec j == uint (K' (nat j))"
abbreviation r_l_spec :: " int => int " where
  "r_l_spec j == int (r (nat j))"
abbreviation r_r_spec :: " int => int " where
  "r_r_spec j == int (r' (nat j))"
abbreviation s_l_spec :: " int => int " where
  "s_l_spec j == int (s (nat j))"
abbreviation s_r_spec :: " int => int " where
  "s_r_spec j == int (s' (nat j))"
abbreviation f_spec :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "f_spec j x y z ==
    uint (f (nat j) (word_of_int x::word32) (word_of_int y) (word_of_int z))"

spark_proof_functions
  k_l_spec = k_l_spec
  k_r_spec = k_r_spec
  r_l_spec = r_l_spec
  r_r_spec = r_r_spec
  s_l_spec = s_l_spec
  s_r_spec = s_r_spec
  f_spec = f_spec

end
