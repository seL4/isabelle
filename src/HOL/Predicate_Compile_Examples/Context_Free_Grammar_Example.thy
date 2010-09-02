theory Context_Free_Grammar_Example
imports Code_Prolog
begin

declare mem_def[code_pred_inline]


subsection {* Alternative rules for length *}

definition size_list :: "'a list => nat"
where "size_list = size"

lemma size_list_simps:
  "size_list [] = 0"
  "size_list (x # xs) = Suc (size_list xs)"
by (auto simp add: size_list_def)

declare size_list_simps[code_pred_def]
declare size_list_def[symmetric, code_pred_inline]


setup {* Quickcheck.add_generator ("prolog", Code_Prolog.quickcheck) *}

datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

lemma
  "w \<in> S\<^isub>1 \<Longrightarrow> w = []"
quickcheck[generator = prolog, iterations=1, expect = counterexample]
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
  limited_types = [],
  limited_predicates = [(["s1", "a1", "b1"], 2)],
  replacing = [(("s1", "limited_s1"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])],
  prolog_system = Code_Prolog.SWI_PROLOG}) *}


theorem S\<^isub>1_sound:
"w \<in> S\<^isub>1 \<Longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator = prolog, iterations=1, expect = counterexample]
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
  limited_types = [],
  limited_predicates = [(["s2", "a2", "b2"], 3)],
  replacing = [(("s2", "limited_s2"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])],
  prolog_system = Code_Prolog.SWI_PROLOG}) *}


theorem S\<^isub>2_sound:
"w \<in> S\<^isub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=prolog, iterations=1, expect = counterexample]
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
  limited_types = [],
  limited_predicates = [(["s3", "a3", "b3"], 6)],
  replacing = [(("s3", "limited_s3"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])],
  prolog_system = Code_Prolog.SWI_PROLOG}) *}

lemma S\<^isub>3_sound:
"w \<in> S\<^isub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=prolog, iterations=1, size=1, expect = no_counterexample]
oops


(*
setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = [],
  prolog_system = Code_Prolog.SWI_PROLOG}) *}


theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>3"
quickcheck[generator = prolog, size=1, iterations=1]
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
  limited_types = [],
  limited_predicates = [(["s4", "a4", "b4"], 6)],
  replacing = [(("s4", "limited_s4"), "quickcheck")],
  manual_reorder = [(("quickcheck", 1), [0,2,1,4,3,5])],
  prolog_system = Code_Prolog.SWI_PROLOG}) *}


theorem S\<^isub>4_sound:
"w \<in> S\<^isub>4 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator = prolog, size=1, iterations=1, expect = no_counterexample]
oops

(*
theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
oops
*)

hide_const a b


end