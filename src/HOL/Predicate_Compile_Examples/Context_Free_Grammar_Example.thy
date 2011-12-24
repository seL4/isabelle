theory Context_Free_Grammar_Example
imports "~~/src/HOL/Library/Code_Prolog"
begin
(*
declare mem_def[code_pred_inline]
*)

subsection {* Alternative rules for length *}

definition size_list :: "'a list => nat"
where "size_list = size"

lemma size_list_simps:
  "size_list [] = 0"
  "size_list (x # xs) = Suc (size_list xs)"
by (auto simp add: size_list_def)

declare size_list_simps[code_pred_def]
declare size_list_def[symmetric, code_pred_inline]


setup {* Context.theory_map (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals))) *}

datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

lemma
  "S\<^isub>1p w \<Longrightarrow> w = []"
quickcheck[tester = prolog, iterations=1, expect = counterexample]
oops

definition "filter_a = filter (\<lambda>x. x = a)"

lemma [code_pred_def]: "filter_a [] = []"
unfolding filter_a_def by simp

lemma [code_pred_def]: "filter_a (x#xs) = (if x = a then x # filter_a xs else filter_a xs)"
unfolding filter_a_def by simp

declare filter_a_def[symmetric, code_pred_inline]

definition "filter_b = filter (\<lambda>x. x = b)"

lemma [code_pred_def]: "filter_b [] = []"
unfolding filter_b_def by simp

lemma [code_pred_def]: "filter_b (x#xs) = (if x = b then x # filter_b xs else filter_b xs)"
unfolding filter_b_def by simp

declare filter_b_def[symmetric, code_pred_inline]

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [(["s1p", "a1p", "b1p"], 2)],
  replacing = [(("s1p", "limited_s1p"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])]}) *}


theorem S\<^isub>1_sound:
"S\<^isub>1p w \<Longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[tester = prolog, iterations=1, expect = counterexample]
oops


inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"


setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [(["s2p", "a2p", "b2p"], 3)],
  replacing = [(("s2p", "limited_s2p"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])]}) *}


theorem S\<^isub>2_sound:
  "S\<^isub>2p w \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[tester = prolog, iterations=1, expect = counterexample]
oops

inductive_set S\<^isub>3 and A\<^isub>3 and B\<^isub>3 where
  "[] \<in> S\<^isub>3"
| "w \<in> A\<^isub>3 \<Longrightarrow> b # w \<in> S\<^isub>3"
| "w \<in> B\<^isub>3 \<Longrightarrow> a # w \<in> S\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> a # w \<in> A\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> b # w \<in> B\<^isub>3"
| "\<lbrakk>v \<in> B\<^isub>3; w \<in> B\<^isub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>3"


setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [(["s3p", "a3p", "b3p"], 6)],
  replacing = [(("s3p", "limited_s3p"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])]}) *}

lemma S\<^isub>3_sound:
  "S\<^isub>3p w \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[tester = prolog, iterations=1, size=1, expect = no_counterexample]
oops


(*
setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = [],
  timeout = seconds 10.0,
  prolog_system = Code_Prolog.SWI_PROLOG}) *}


theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>3"
quickcheck[tester = prolog, size=1, iterations=1]
oops
*)

inductive_set S\<^isub>4 and A\<^isub>4 and B\<^isub>4 where
  "[] \<in> S\<^isub>4"
| "w \<in> A\<^isub>4 \<Longrightarrow> b # w \<in> S\<^isub>4"
| "w \<in> B\<^isub>4 \<Longrightarrow> a # w \<in> S\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> a # w \<in> A\<^isub>4"
| "\<lbrakk>v \<in> A\<^isub>4; w \<in> A\<^isub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> b # w \<in> B\<^isub>4"
| "\<lbrakk>v \<in> B\<^isub>4; w \<in> B\<^isub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>4"


setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [(["s4p", "a4p", "b4p"], 6)],
  replacing = [(("s4p", "limited_s4p"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])]}) *}


theorem S\<^isub>4_sound:
  "S\<^isub>4p w \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[tester = prolog, size=1, iterations=1, expect = no_counterexample]
oops

(*
theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
oops
*)

hide_const a b


end