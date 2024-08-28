(* Author: Andreas Lochbihler, Digital Asset *)

section \<open>Laziness tests\<close>

theory Code_Lazy_Test imports
  "HOL-Library.Code_Lazy"
  "HOL-Library.Stream" 
  "HOL-Library.Code_Test"
  "HOL-Library.BNF_Corec"
begin

subsection \<open>Linear codatatype\<close>

code_lazy_type stream

value [code] "cycle ''ab''"
value [code] "let x = cycle ''ab''; y = snth x 10 in x"

datatype 'a llist = LNil ("\<^bold>[\<^bold>]") | LCons (lhd: 'a) (ltl: "'a llist") (infixr "\<^bold>#" 65)

subsection \<open>Finite lazy lists\<close>

code_lazy_type llist

no_notation lazy_llist ("_")
nonterminal llist_args
syntax
  "" :: "'a \<Rightarrow> llist_args"  ("_")
  "_llist_args" :: "'a \<Rightarrow> llist_args \<Rightarrow> llist_args"  ("_,/ _")
  "_llist" :: "llist_args => 'a list"    ("\<^bold>[(_)\<^bold>]")
syntax_consts
  "_llist_args" "_llist" == lazy_llist
translations
  "\<^bold>[x, xs\<^bold>]" == "x\<^bold>#\<^bold>[xs\<^bold>]"
  "\<^bold>[x\<^bold>]" == "x\<^bold>#\<^bold>[\<^bold>]"
  "\<^bold>[x\<^bold>]" == "CONST lazy_llist x"

definition llist :: "nat llist" where
  "llist = \<^bold>[1, 2, 3, hd [], 4\<^bold>]"

fun lnth :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a" where
  "lnth 0 (x \<^bold># xs) = x"
| "lnth (Suc n) (x \<^bold># xs) = lnth n xs"

value [code] "llist"
value [code] "let x = lnth 2 llist in (x, llist)"
value [code] "llist"

fun lfilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "lfilter P \<^bold>[\<^bold>] = \<^bold>[\<^bold>]"
| "lfilter P (x \<^bold># xs) = (if P x then x \<^bold># lfilter P xs else lfilter P xs)"

value [code] "lhd (lfilter odd llist)"

definition lfilter_test :: "nat llist \<Rightarrow> _" where "lfilter_test xs = lhd (lfilter even xs)"
  \<comment> \<open>Filtering \<^term>\<open>llist\<close> for \<^term>\<open>even\<close> fails because only the datatype is lazy, not the
  filter function itself.\<close>
ML_val \<open> (@{code lfilter_test} @{code llist}; raise Fail "Failure expected") handle Match => () \<close>

subsection \<open>Records as free type\<close>

record ('a, 'b) rec = 
  rec1 :: 'a
  rec2 :: 'b

free_constructors rec_ext for rec.rec_ext
  subgoal by(rule rec.cases_scheme)
  subgoal by(rule rec.ext_inject)
  done

code_lazy_type rec_ext

definition rec_test1 where "rec_test1 = rec1 (\<lparr>rec1 = Suc 5, rec2 = True\<rparr>\<lparr>rec1 := 0\<rparr>)"
definition rec_test2 :: "(bool, bool) rec" where "rec_test2 = \<lparr>rec1 = hd [], rec2 = True\<rparr>"
test_code "rec_test1 = 0" in PolyML Scala
value [code] "rec_test2"

subsection \<open>Branching codatatypes\<close>

codatatype tree = L | Node tree tree (infix "\<triangle>" 900)

code_lazy_type tree

fun mk_tree :: "nat \<Rightarrow> tree" where
  mk_tree_0: "mk_tree 0 = L"
|            "mk_tree (Suc n) = (let t = mk_tree n in t \<triangle> t)"

function subtree :: "bool list \<Rightarrow> tree \<Rightarrow> tree" where
  "subtree [] t = t"
| "subtree (True # p) (l \<triangle> r) = subtree p l"
| "subtree (False # p) (l \<triangle> r) = subtree p r"
| "subtree _ L = L"
  by pat_completeness auto
termination by lexicographic_order

value [code] "mk_tree 10"
value [code] "let t = mk_tree 10; _ = subtree [True, True, False, False] t in t"

lemma mk_tree_Suc: "mk_tree (Suc n) = mk_tree n \<triangle> mk_tree n"
  by(simp add: Let_def)
lemmas [code] = mk_tree_0 mk_tree_Suc
value [code] "let t = mk_tree 10; _ = subtree [True, True, False, False] t in t"
value [code] "let t = mk_tree 4; _ = subtree [True, True, False, False] t in t"

subsection \<open>Corecursion\<close>

corec (friend) plus :: "'a :: plus stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "plus xs ys = (shd xs + shd ys) ## plus (stl xs) (stl ys)"

corec (friend) times :: "'a :: {plus, times} stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "times xs ys = (shd xs * shd ys) ## plus (times (stl xs) ys) (times xs (stl ys))"

subsection \<open>Pattern-matching tests\<close>

definition f1 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat llist \<Rightarrow> unit" where
  "f1 _ _ _ _ = ()"

declare [[code drop: f1]]
lemma f1_code1 [code]: 
  "f1 b c d    ns     = Code.abort (STR ''4'') (\<lambda>_. ())" 
  "f1 b c True \<^bold>[n, m\<^bold>] = Code.abort (STR ''3'') (\<lambda>_. ())" 
  "f1 b True d \<^bold>[n\<^bold>]    = Code.abort (STR ''2'') (\<lambda>_. ())" 
  "f1 True c d \<^bold>[\<^bold>]     = ()"
  by(simp_all add: f1_def)

value [code] "f1 True False False \<^bold>[\<^bold>]"
deactivate_lazy_type llist
value [code] "f1 True False False \<^bold>[\<^bold>]"
declare f1_code1(1) [code del]
value [code] "f1 True False False \<^bold>[\<^bold>]"
activate_lazy_type llist
value [code] "f1 True False False \<^bold>[\<^bold>]"

declare [[code drop: f1]]
lemma f1_code2 [code]: 
  "f1 b c d    ns     = Code.abort (STR ''4'') (\<lambda>_. ())" 
  "f1 b c True \<^bold>[n, m\<^bold>] = Code.abort (STR ''3'') (\<lambda>_. ())" 
  "f1 b True d \<^bold>[n\<^bold>]    = ()"
  "f1 True c d \<^bold>[\<^bold>]     = Code.abort (STR ''1'') (\<lambda>_. ())"
  by(simp_all add: f1_def)

value [code] "f1 True True True \<^bold>[0\<^bold>]"
declare f1_code2(1)[code del]
value [code] "f1 True True True \<^bold>[0\<^bold>]"

declare [[code drop: f1]]
lemma f1_code3 [code]:
  "f1 b c d    ns     = Code.abort (STR ''4'') (\<lambda>_. ())"
  "f1 b c True \<^bold>[n, m\<^bold>] = ()" 
  "f1 b True d \<^bold>[n\<^bold>]    = Code.abort (STR ''2'') (\<lambda>_. ())"
  "f1 True c d \<^bold>[\<^bold>]     = Code.abort (STR ''1'') (\<lambda>_. ())"
  by(simp_all add: f1_def)

value [code] "f1 True True True \<^bold>[0, 1\<^bold>]"
declare f1_code3(1)[code del]
value [code] "f1 True True True \<^bold>[0, 1\<^bold>]"

declare [[code drop: f1]]
lemma f1_code4 [code]:
  "f1 b c d    ns     = ()" 
  "f1 b c True \<^bold>[n, m\<^bold>] = Code.abort (STR ''3'') (\<lambda>_. ())"
  "f1 b True d \<^bold>[n\<^bold>]    = Code.abort (STR ''2'') (\<lambda>_. ())" 
  "f1 True c d \<^bold>[\<^bold>]     = Code.abort (STR ''1'') (\<lambda>_. ())"
  by(simp_all add: f1_def)

value [code] "f1 True True True \<^bold>[0, 1, 2\<^bold>]"
value [code] "f1 True True False \<^bold>[0, 1\<^bold>]"
value [code] "f1 True False True \<^bold>[0\<^bold>]"
value [code] "f1 False True True \<^bold>[\<^bold>]"

definition f2 :: "nat llist llist list \<Rightarrow> unit" where "f2 _ = ()"

declare [[code drop: f2]]
lemma f2_code1 [code]:
  "f2 xs = Code.abort (STR ''a'') (\<lambda>_. ())"
  "f2 [\<^bold>[\<^bold>[\<^bold>]\<^bold>]] = ()"
  "f2 [\<^bold>[\<^bold>[Suc n\<^bold>]\<^bold>]] = ()"
  "f2 [\<^bold>[\<^bold>[0, Suc n\<^bold>]\<^bold>]] = ()"
  by(simp_all add: f2_def)

value [code] "f2 [\<^bold>[\<^bold>[\<^bold>]\<^bold>]]"
value [code] "f2 [\<^bold>[\<^bold>[4\<^bold>]\<^bold>]]"
value [code] "f2 [\<^bold>[\<^bold>[0, 1\<^bold>]\<^bold>]]"
ML_val \<open> (@{code f2} []; error "Fail expected") handle Fail _ => () \<close>

definition f3 :: "nat set llist \<Rightarrow> unit" where "f3 _ = ()"

declare [[code drop: f3]]
lemma f3_code1 [code]:
  "f3 \<^bold>[\<^bold>] = ()"
  "f3 \<^bold>[A\<^bold>] = ()"
  by(simp_all add: f3_def)

value [code] "f3 \<^bold>[\<^bold>]"
value [code] "f3 \<^bold>[{}\<^bold>]"
value [code] "f3 \<^bold>[UNIV\<^bold>]"

end