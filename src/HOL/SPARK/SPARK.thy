(*  Title:      HOL/SPARK/SPARK.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Declaration of proof functions for SPARK/Ada verification environment.
*)

theory SPARK
imports SPARK_Setup
begin

text \<open>Bitwise logical operators\<close>

spark_proof_functions
  bit__and (integer, integer) : integer = Bit_Operations.and
  bit__or (integer, integer) : integer = Bit_Operations.or
  bit__xor (integer, integer) : integer = Bit_Operations.xor

lemmas [simp] =
  OR_upper [of _ 8, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 8, simplified]
  OR_upper [of _ 16, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 16, simplified]
  OR_upper [of _ 32, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 32, simplified]
  OR_upper [of _ 64, simplified zle_diff1_eq [symmetric], simplified]
  OR_upper [of _ 64, simplified]

lemmas [simp] =
  XOR_upper [of _ 8, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 8, simplified]
  XOR_upper [of _ 16, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 16, simplified]
  XOR_upper [of _ 32, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 32, simplified]
  XOR_upper [of _ 64, simplified zle_diff1_eq [symmetric], simplified]
  XOR_upper [of _ 64, simplified]

lemma bit_not_spark_eq:
  "Bit_Operations.not (word_of_int x :: ('a::len) word) =
  word_of_int (2 ^ LENGTH('a) - 1 - x)"
  by (simp flip: mask_eq_exp_minus_1 add: of_int_mask_eq not_eq_complement)

lemmas [simp] =
  bit_not_spark_eq [where 'a=8, simplified]
  bit_not_spark_eq [where 'a=16, simplified]
  bit_not_spark_eq [where 'a=32, simplified]
  bit_not_spark_eq [where 'a=64, simplified]


text \<open>Minimum and maximum\<close>

spark_proof_functions
  integer__min = "min :: int \<Rightarrow> int \<Rightarrow> int"
  integer__max = "max :: int \<Rightarrow> int \<Rightarrow> int"

end

