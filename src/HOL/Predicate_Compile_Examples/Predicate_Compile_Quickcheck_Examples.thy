theory Predicate_Compile_Quickcheck_Examples
imports "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
begin

section {* Sets *}

lemma "x \<in> {(1::nat)} ==> False"
quickcheck[generator=predicate_compile_wo_ff, iterations=10]
oops

lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x \<noteq> Suc 0"
quickcheck[generator=predicate_compile_wo_ff]
oops

lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x = Suc 0"
quickcheck[generator=predicate_compile_wo_ff]
oops
 
lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x <= Suc 0"
quickcheck[generator=predicate_compile_wo_ff]
oops

section {* Numerals *}

lemma
  "x \<in> {1, 2, (3::nat)} ==> x = 1 \<or> x = 2"
quickcheck[generator=predicate_compile_wo_ff]
oops

lemma "x \<in> {1, 2, (3::nat)} ==> x < 3"
quickcheck[generator=predicate_compile_wo_ff]
oops

lemma
  "x \<in> {1, 2} \<union> {3, 4} ==> x = (1::nat) \<or> x = (2::nat)"
quickcheck[generator=predicate_compile_wo_ff]
oops

section {* Equivalences *}

inductive is_ten :: "nat => bool"
where
  "is_ten 10"

inductive is_eleven :: "nat => bool"
where
  "is_eleven 11"

lemma
  "is_ten x = is_eleven x"
quickcheck[tester = predicate_compile_wo_ff, iterations = 1, size = 1, expect = counterexample]
oops

section {* Context Free Grammar *}

datatype alphabet = a | b

inductive_set S\<^sub>1 and A\<^sub>1 and B\<^sub>1 where
  "[] \<in> S\<^sub>1"
| "w \<in> A\<^sub>1 \<Longrightarrow> b # w \<in> S\<^sub>1"
| "w \<in> B\<^sub>1 \<Longrightarrow> a # w \<in> S\<^sub>1"
| "w \<in> S\<^sub>1 \<Longrightarrow> a # w \<in> A\<^sub>1"
| "w \<in> S\<^sub>1 \<Longrightarrow> b # w \<in> S\<^sub>1"
| "\<lbrakk>v \<in> B\<^sub>1; v \<in> B\<^sub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>1"

lemma
  "w \<in> S\<^sub>1 \<Longrightarrow> w = []"
quickcheck[tester = predicate_compile_ff_nofs, iterations=1]
oops

theorem S\<^sub>1_sound:
"w \<in> S\<^sub>1 \<Longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile_ff_nofs, size=15]
oops


inductive_set S\<^sub>2 and A\<^sub>2 and B\<^sub>2 where
  "[] \<in> S\<^sub>2"
| "w \<in> A\<^sub>2 \<Longrightarrow> b # w \<in> S\<^sub>2"
| "w \<in> B\<^sub>2 \<Longrightarrow> a # w \<in> S\<^sub>2"
| "w \<in> S\<^sub>2 \<Longrightarrow> a # w \<in> A\<^sub>2"
| "w \<in> S\<^sub>2 \<Longrightarrow> b # w \<in> B\<^sub>2"
| "\<lbrakk>v \<in> B\<^sub>2; v \<in> B\<^sub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>2"
(*
code_pred [random_dseq inductify] S\<^sub>2 .
thm S\<^sub>2.random_dseq_equation
thm A\<^sub>2.random_dseq_equation
thm B\<^sub>2.random_dseq_equation

values [random_dseq 1, 2, 8] 10 "{x. S\<^sub>2 x}"

lemma "w \<in> S\<^sub>2 ==> w \<noteq> [] ==> w \<noteq> [b, a] ==> w \<in> {}"
quickcheck[generator=predicate_compile, size=8]
oops

lemma "[x <- w. x = a] = []"
quickcheck[generator=predicate_compile]
oops

declare list.size(3,4)[code_pred_def]

(*
lemma "length ([x \<leftarrow> w. x = a]) = (0::nat)"
quickcheck[generator=predicate_compile]
oops
*)

lemma
"w \<in> S\<^sub>2 ==> length [x \<leftarrow> w. x = a] <= Suc (Suc 0)"
quickcheck[generator=predicate_compile, size = 10, iterations = 1]
oops
*)
theorem S\<^sub>2_sound:
"w \<in> S\<^sub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile_ff_nofs, size=5, iterations=10]
oops

inductive_set S\<^sub>3 and A\<^sub>3 and B\<^sub>3 where
  "[] \<in> S\<^sub>3"
| "w \<in> A\<^sub>3 \<Longrightarrow> b # w \<in> S\<^sub>3"
| "w \<in> B\<^sub>3 \<Longrightarrow> a # w \<in> S\<^sub>3"
| "w \<in> S\<^sub>3 \<Longrightarrow> a # w \<in> A\<^sub>3"
| "w \<in> S\<^sub>3 \<Longrightarrow> b # w \<in> B\<^sub>3"
| "\<lbrakk>v \<in> B\<^sub>3; w \<in> B\<^sub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>3"

code_pred [inductify, skip_proof] S\<^sub>3 .
thm S\<^sub>3.equation
(*
values 10 "{x. S\<^sub>3 x}"
*)


lemma S\<^sub>3_sound:
"w \<in> S\<^sub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile_ff_fs, size=10, iterations=10]
oops

lemma "\<not> (length w > 2) \<or> \<not> (length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b])"
quickcheck[size=10, tester = predicate_compile_ff_fs]
oops

theorem S\<^sub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. b = x] \<longrightarrow> w \<in> S\<^sub>3"
(*quickcheck[generator=SML]*)
quickcheck[generator=predicate_compile_ff_fs, size=10, iterations=100]
oops


inductive_set S\<^sub>4 and A\<^sub>4 and B\<^sub>4 where
  "[] \<in> S\<^sub>4"
| "w \<in> A\<^sub>4 \<Longrightarrow> b # w \<in> S\<^sub>4"
| "w \<in> B\<^sub>4 \<Longrightarrow> a # w \<in> S\<^sub>4"
| "w \<in> S\<^sub>4 \<Longrightarrow> a # w \<in> A\<^sub>4"
| "\<lbrakk>v \<in> A\<^sub>4; w \<in> A\<^sub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^sub>4"
| "w \<in> S\<^sub>4 \<Longrightarrow> b # w \<in> B\<^sub>4"
| "\<lbrakk>v \<in> B\<^sub>4; w \<in> B\<^sub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>4"

theorem S\<^sub>4_sound:
"w \<in> S\<^sub>4 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[tester = predicate_compile_ff_nofs, size=5, iterations=1]
oops

theorem S\<^sub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^sub>4"
quickcheck[tester = predicate_compile_ff_nofs, size=5, iterations=1]
oops

hide_const a b

subsection {* Lexicographic order *}
(* TODO *)
(*
lemma
  "(u, v) : lexord r ==> (x @ u, y @ v) : lexord r"
oops
*)
subsection {* IMP *}

type_synonym var = nat
type_synonym state = "int list"

datatype com =
  Skip |
  Ass var "int" |
  Seq com com |
  IF "state list" com com |
  While "state list" com

inductive exec :: "com => state => state => bool" where
  "exec Skip s s" |
  "exec (Ass x e) s (s[x := e])" |
  "exec c1 s1 s2 ==> exec c2 s2 s3 ==> exec (Seq c1 c2) s1 s3" |
  "s \<in> set b ==> exec c1 s t ==> exec (IF b c1 c2) s t" |
  "s \<notin> set b ==> exec c2 s t ==> exec (IF b c1 c2) s t" |
  "s \<notin> set b ==> exec (While b c) s s" |
  "s1 \<in> set b ==> exec c s1 s2 ==> exec (While b c) s2 s3 ==> exec (While b c) s1 s3"

code_pred [random_dseq] exec .

values [random_dseq 1, 2, 3] 10 "{(c, s, s'). exec c s s'}"

lemma
  "exec c s s' ==> exec (Seq c c) s s'"
  quickcheck[tester = predicate_compile_wo_ff, size=2, iterations=20, expect = counterexample]
oops

subsection {* Lambda *}

datatype type =
    Atom nat
  | Fun type type    (infixr "\<Rightarrow>" 200)

datatype dB =
    Var nat
  | App dB dB (infixl "\<degree>" 200)
  | Abs type dB

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>" [90, 0] 91)
where
  "[]\<langle>i\<rangle> = None"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

inductive nth_el' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
where
  "nth_el' (x # xs) 0 x"
| "nth_el' xs i y \<Longrightarrow> nth_el' (x # xs) (Suc i) y"

inductive typing :: "type list \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
  where
    Var [intro!]: "nth_el' env x T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "T # env \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs T t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : U \<Rightarrow> T \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

primrec
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs T s) k = Abs T (lift s (k + 1))"

primrec
  subst :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
where
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (i - 1) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs T t)[s/k] = Abs T (t[lift s 0 / k+1])"

inductive beta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "Abs T s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs T s \<rightarrow>\<^sub>\<beta> Abs T t"

lemma
  "\<Gamma> \<turnstile> t : U \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : U"
quickcheck[tester = predicate_compile_ff_fs, size = 7, iterations = 10]
oops

subsection {* JAD *}

definition matrix :: "('a :: semiring_0) list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "matrix M rs cs \<longleftrightarrow> (\<forall> row \<in> set M. length row = cs) \<and> length M = rs"
(*
code_pred [random_dseq inductify] matrix .
thm matrix.random_dseq_equation

thm matrix_aux.random_dseq_equation

values [random_dseq 3, 2] 10 "{(M, rs, cs). matrix (M:: int list list) rs cs}"
*)
lemma [code_pred_intro]:
  "matrix [] 0 m"
  "matrix xss n m ==> length xs = m ==> matrix (xs # xss) (Suc n) m"
proof -
  show "matrix [] 0 m" unfolding matrix_def by auto
next
  show "matrix xss n m ==> length xs = m ==> matrix (xs # xss) (Suc n) m"
    unfolding matrix_def by auto
qed

code_pred [random_dseq inductify] matrix
  apply (cases x)
  unfolding matrix_def apply fastforce
  apply fastforce done


values [random_dseq 2, 2, 15] 6 "{(M::int list list, n, m). matrix M n m}"

definition "scalar_product v w = (\<Sum> (x, y)\<leftarrow>zip v w. x * y)"

definition mv :: "('a \<Colon> semiring_0) list list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where [simp]: "mv M v = map (scalar_product v) M"
text {*
  This defines the matrix vector multiplication. To work properly @{term
"matrix M m n \<and> length v = n"} must hold.
*}

subsection "Compressed matrix"

definition "sparsify xs = [i \<leftarrow> zip [0..<length xs] xs. snd i \<noteq> 0]"
(*
lemma sparsify_length: "(i, x) \<in> set (sparsify xs) \<Longrightarrow> i < length xs"
  by (auto simp: sparsify_def set_zip)

lemma listsum_sparsify[simp]:
  fixes v :: "('a \<Colon> semiring_0) list"
  assumes "length w = length v"
  shows "(\<Sum>x\<leftarrow>sparsify w. (\<lambda>(i, x). v ! i) x * snd x) = scalar_product v w"
    (is "(\<Sum>x\<leftarrow>_. ?f x) = _")
  unfolding sparsify_def scalar_product_def
  using assms listsum_map_filter[where f="?f" and P="\<lambda> i. snd i \<noteq> (0::'a)"]
  by (simp add: listsum_setsum)
*)
definition [simp]: "unzip w = (map fst w, map snd w)"

primrec insert :: "('a \<Rightarrow> 'b \<Colon> linorder) => 'a \<Rightarrow> 'a list => 'a list" where
  "insert f x [] = [x]" |
  "insert f x (y # ys) = (if f y < f x then y # insert f x ys else x # y # ys)"

primrec sort :: "('a \<Rightarrow> 'b \<Colon> linorder) \<Rightarrow> 'a list => 'a list" where
  "sort f [] = []" |
  "sort f (x # xs) = insert f x (sort f xs)"

definition
  "length_permutate M = (unzip o sort (length o snd)) (zip [0 ..< length M] M)"
(*
definition
  "transpose M = [map (\<lambda> xs. xs ! i) (takeWhile (\<lambda> xs. i < length xs) M). i \<leftarrow> [0 ..< length (M ! 0)]]"
*)
definition
  "inflate upds = foldr (\<lambda> (i, x) upds. upds[i := x]) upds (replicate (length upds) 0)"

definition
  "jad = apsnd transpose o length_permutate o map sparsify"

definition
  "jad_mv v = inflate o split zip o apsnd (map listsum o transpose o map (map (\<lambda> (i, x). v ! i * x)))"

lemma "matrix (M::int list list) rs cs \<Longrightarrow> False"
quickcheck[tester = predicate_compile_ff_nofs, size = 6]
oops

lemma
  "\<lbrakk> matrix M rs cs ; length v = cs \<rbrakk> \<Longrightarrow> jad_mv v (jad M) = mv M v"
quickcheck[tester = predicate_compile_wo_ff]
oops

end
