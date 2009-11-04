theory Predicate_Compile_Quickcheck_ex
imports Predicate_Compile_Quickcheck
  Predicate_Compile_Alternative_Defs
begin

section {* Sets *}

lemma "x \<in> {(1::nat)} ==> False"
quickcheck[generator=predicate_compile]
oops

lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x \<noteq> Suc 0"
oops

lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x = Suc 0"
quickcheck[generator=predicate_compile]
oops
 
lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x <= Suc 0"
quickcheck[generator=predicate_compile]
oops

section {* Numerals *}

lemma
  "x \<in> {1, 2, (3::nat)} ==> x < 3"
(*quickcheck[generator=predicate_compile]*)
oops
lemma
  "x \<in> {1, 2} \<union> {3, 4} ==> x > 4"
(*quickcheck[generator=predicate_compile]*)
oops

section {* Context Free Grammar *}

datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

theorem S\<^isub>1_sound:
"w \<in> S\<^isub>1p \<Longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
(*quickcheck[generator=predicate_compile, size=15]*)
oops


inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"

code_pred [inductify, random] S\<^isub>2 .
thm S\<^isub>2.random_equation
thm A\<^isub>2.random_equation
thm B\<^isub>2.random_equation

values [random] 10 "{x. S\<^isub>2 x}"

lemma "w \<in> S\<^isub>2 ==> w \<noteq> [] ==> w \<noteq> [b, a] ==> w \<in> {}"
quickcheck[generator=predicate_compile]
oops

lemma "[x <- w. x = a] = []"
quickcheck[generator=predicate_compile]
oops


lemma "length ([x \<leftarrow> w. x = a]) = (0::nat)"
(*quickcheck[generator=predicate_compile]*)
oops



lemma
"w \<in> S\<^isub>2 ==> length [x \<leftarrow> w. x = a] < Suc (Suc 0)"
(*quickcheck[generator=predicate_compile]*)
oops


theorem S\<^isub>2_sound:
"w \<in> S\<^isub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
(*quickcheck[generator=predicate_compile, size=15, iterations=100]*)
oops

inductive_set S\<^isub>3 and A\<^isub>3 and B\<^isub>3 where
  "[] \<in> S\<^isub>3"
| "w \<in> A\<^isub>3 \<Longrightarrow> b # w \<in> S\<^isub>3"
| "w \<in> B\<^isub>3 \<Longrightarrow> a # w \<in> S\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> a # w \<in> A\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> b # w \<in> B\<^isub>3"
| "\<lbrakk>v \<in> B\<^isub>3; w \<in> B\<^isub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>3"

code_pred [inductify] S\<^isub>3 .
thm S\<^isub>3.equation

values 10 "{x. S\<^isub>3 x}"

lemma S\<^isub>3_sound:
"w \<in> S\<^isub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
(*quickcheck[generator=predicate_compile, size=10, iterations=1]*)
oops


lemma "\<not> (length w > 2) \<or> \<not> (length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b])"
(*quickcheck[size=10, generator = pred_compile]*)
oops

theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. b = x] \<longrightarrow> w \<in> S\<^isub>3"
(*quickcheck[generator=SML]*)
(*quickcheck[generator=predicate_compile, size=10, iterations=100]*)
oops


inductive_set S\<^isub>4 and A\<^isub>4 and B\<^isub>4 where
  "[] \<in> S\<^isub>4"
| "w \<in> A\<^isub>4 \<Longrightarrow> b # w \<in> S\<^isub>4"
| "w \<in> B\<^isub>4 \<Longrightarrow> a # w \<in> S\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> a # w \<in> A\<^isub>4"
| "\<lbrakk>v \<in> A\<^isub>4; w \<in> A\<^isub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> b # w \<in> B\<^isub>4"
| "\<lbrakk>v \<in> B\<^isub>4; w \<in> B\<^isub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>4"

theorem S\<^isub>4_sound:
"w \<in> S\<^isub>4 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
(*quickcheck[generator = predicate_compile, size=2, iterations=1]*)
oops

theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
(*quickcheck[generator = pred_compile, size=5, iterations=1]*)
oops


end