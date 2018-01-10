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
  bit__and (integer, integer) : integer = "(AND)"
  bit__or (integer, integer) : integer = "(OR)"
  bit__xor (integer, integer) : integer = "(XOR)"

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
  "NOT (word_of_int x :: ('a::len0) word) =
  word_of_int (2 ^ len_of TYPE('a) - 1 - x)"
proof -
  have "word_of_int x + NOT (word_of_int x) =
    word_of_int x + (word_of_int (2 ^ len_of TYPE('a) - 1 - x)::'a word)"
    by (simp only: bwsimps bin_add_not Min_def)
      (simp add: word_of_int_hom_syms word_of_int_2p_len)
  then show ?thesis by (rule add_left_imp_eq)
qed

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

