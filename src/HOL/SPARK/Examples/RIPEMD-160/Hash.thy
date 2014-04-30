(*  Title:      HOL/SPARK/Examples/RIPEMD-160/Hash.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory Hash
imports RMD_Specification
begin

spark_open "rmd/hash"

abbreviation from_chain :: "chain \<Rightarrow> RMD.chain" where
  "from_chain c \<equiv> (
    word_of_int (h0 c),
    word_of_int (h1 c),
    word_of_int (h2 c),
    word_of_int (h3 c),
    word_of_int (h4 c))"

abbreviation to_chain :: "RMD.chain \<Rightarrow> chain" where
  "to_chain c \<equiv>
    (let (h0, h1, h2, h3, h4) = c in
      (|h0 = uint h0,
        h1 = uint h1,
        h2 = uint h2,
        h3 = uint h3,
        h4 = uint h4|))"

abbreviation round' :: "chain \<Rightarrow> block \<Rightarrow> chain" where
  "round' c b == to_chain (round (\<lambda>n. word_of_int (b (int n))) (from_chain c))"

abbreviation rounds' :: "chain \<Rightarrow> int \<Rightarrow> message \<Rightarrow> chain" where
  "rounds' h i X ==
     to_chain (rounds
      (\<lambda>n. \<lambda>m. word_of_int (X (int n) (int m)))
      (from_chain h)
      (nat i))"

abbreviation rmd_hash :: "message \<Rightarrow> int \<Rightarrow> chain" where
  "rmd_hash X i == to_chain (rmd
    (\<lambda>n. \<lambda>m. word_of_int (X (int n) (int m)))
    (nat i))"

spark_proof_functions
  round_spec = round'
  rounds = rounds'
  rmd_hash = rmd_hash

spark_vc function_hash_12
  using H1 H6
  by (simp add:
    rounds_def rmd_body_def round_def
    h_0_def h0_0_def h1_0_def h2_0_def h3_0_def h4_0_def)


lemma rounds_step:
  assumes "0 <= i"
  shows "rounds X b (Suc i) = round (X i) (rounds X b i)"
  by (simp add: rounds_def rmd_body_def)

lemma from_to_id: "from_chain (to_chain C) = C"
proof (cases C)
  fix a b c d e f::word32
  assume "C = (a, b, c, d, e)"
  thus ?thesis by (cases a) simp
qed

lemma steps_to_steps':
  "round X (foldl a b c) = round X (from_chain (to_chain (foldl a b c)))"
  unfolding from_to_id ..

lemma rounds'_step:
  assumes "0 <= i"
  shows "rounds' c (i + 1) x = round' (rounds' c i x) (x i)"
proof -
  have makesuc: "nat (i + 1) = Suc (nat i)" using assms by simp
  show ?thesis using assms
    by (simp add: makesuc rounds_def rmd_body_def steps_to_steps')
qed


spark_vc function_hash_13
proof -
  have loop_suc: "loop__1__i + 2 = (loop__1__i + 1) + 1" by simp
  have "0 <= loop__1__i + 1" using `0 <= loop__1__i` by simp
  show ?thesis
    unfolding loop_suc
    unfolding rounds'_step[OF `0 <= loop__1__i + 1`]
    unfolding H1[symmetric]
    unfolding H18 ..
qed


spark_vc function_hash_17
  unfolding rmd_def H1 rounds_def ..

spark_end

end
