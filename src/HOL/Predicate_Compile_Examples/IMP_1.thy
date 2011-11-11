theory IMP_1
imports "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
begin

subsection {* IMP *}

text {*
  In this example, the state is one boolean variable and the commands are Skip, Ass, Seq, and IF.
*}

type_synonym var = unit
type_synonym state = bool

datatype com =
  Skip |
  Ass bool |
  Seq com com |
  IF com com

inductive exec :: "com => state => state => bool" where
  "exec Skip s s" |
  "exec (Ass e) s e" |
  "exec c1 s1 s2 ==> exec c2 s2 s3 ==> exec (Seq c1 c2) s1 s3" |
  "s ==> exec c1 s t ==> exec (IF c1 c2) s t" |
  "\<not> s ==> exec c2 s t ==> exec (IF c1 c2) s t"

lemma
  "exec c s s' ==> exec (Seq c c) s s'"
quickcheck[tester = smart_exhaustive, size = 2, iterations = 100, timeout = 600.0, expect = counterexample]
oops


end
