theory Predicate_Compile_Quickcheck_ex
imports Predicate_Compile_Quickcheck
  Predicate_Compile_Alternative_Defs
begin

ML {* Predicate_Compile_Alternative_Defs.get *}

section {* Sets *}
(*
lemma "x \<in> {(1::nat)} ==> False"
quickcheck[generator=predicate_compile, iterations=10]
oops
*)
(* TODO: some error with doubled negation *)
(*
lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x \<noteq> Suc 0"
quickcheck[generator=predicate_compile]
oops
*)
(*
lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x = Suc 0"
quickcheck[generator=predicate_compile]
oops
*) 
lemma "x \<in> {Suc 0, Suc (Suc 0)} ==> x <= Suc 0"
(*quickcheck[generator=predicate_compile]*)
oops

section {* Numerals *}
(*
lemma
  "x \<in> {1, 2, (3::nat)} ==> x = 1 \<or> x = 2"
quickcheck[generator=predicate_compile]
oops
*)
lemma "x \<in> {1, 2, (3::nat)} ==> x < 3"
(*quickcheck[generator=predicate_compile]*)
oops

lemma
  "x \<in> {1, 2} \<union> {3, 4} ==> x = (1::nat) \<or> x = (2::nat)"
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
(*
code_pred [random_dseq inductify] "S\<^isub>1p" .
*)
(*thm B\<^isub>1p.random_dseq_equation*)
(*
values [random_dseq 2, 2, 4] 10 "{x. S\<^isub>1p x}"
values [random_dseq 1, 1, 5] 20 "{x. S\<^isub>1p x}"

ML {* set ML_Context.trace *}
*)
ML {* set Toplevel.debug *}
(*
quickcheck[generator = predicate_compile, size = 10, iterations = 1]
oops
*)
ML {* Spec_Rules.get *}
ML {* Item_Net.retrieve *}
local_setup {* Local_Theory.checkpoint *}
ML {* Predicate_Compile_Data.get_specification @{theory} @{term "append"} *}
lemma
  "w \<in> S\<^isub>1p \<Longrightarrow> w = []"
quickcheck[generator = predicate_compile, iterations=1]
oops

theorem S\<^isub>1_sound:
"w \<in> S\<^isub>1p \<Longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile, size=15]
oops


inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"

code_pred [random_dseq inductify] S\<^isub>2 .
thm S\<^isub>2.random_dseq_equation
thm A\<^isub>2.random_dseq_equation
thm B\<^isub>2.random_dseq_equation

values [random_dseq 1, 2, 8] 10 "{x. S\<^isub>2 x}"

lemma "w \<in> S\<^isub>2 ==> w \<noteq> [] ==> w \<noteq> [b, a] ==> w \<in> {}"
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
"w \<in> S\<^isub>2 ==> length [x \<leftarrow> w. x = a] <= Suc (Suc 0)"
quickcheck[generator=predicate_compile, size = 10, iterations = 1]
oops

theorem S\<^isub>2_sound:
"w \<in> S\<^isub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile, size=15, iterations=1]
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
(*
values 10 "{x. S\<^isub>3 x}"
*)


lemma S\<^isub>3_sound:
"w \<in> S\<^isub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=predicate_compile, size=10, iterations=10]
oops

lemma "\<not> (length w > 2) \<or> \<not> (length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b])"
quickcheck[size=10, generator = predicate_compile]
oops

theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. b = x] \<longrightarrow> w \<in> S\<^isub>3"
(*quickcheck[generator=SML]*)
quickcheck[generator=predicate_compile, size=10, iterations=100]
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
quickcheck[generator = predicate_compile, size=5, iterations=1]
oops

theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
quickcheck[generator = predicate_compile, size=5, iterations=1]
oops

hide const b

subsection {* Lexicographic order *}
lemma
  "(u, v) : lexord r ==> (x @ u, y @ v) : lexord r"

subsection {* IMP *}

types
  var = nat
  state = "int list"

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
quickcheck[generator = predicate_compile, size=3, iterations=1]
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
quickcheck[generator = predicate_compile, size = 7, iterations = 10]
oops

(*
code_pred (expected_modes: i => i => o => bool, i => i => i => bool) typing .
thm typing.equation

code_pred (modes: i => i => bool,  i => o => bool as reduce') beta .
thm beta.equation

values "{x. App (Abs (Atom 0) (Var 0)) (Var 1) \<rightarrow>\<^sub>\<beta> x}"

definition "reduce t = Predicate.the (reduce' t)"

value "reduce (App (Abs (Atom 0) (Var 0)) (Var 1))"

code_pred [random] typing .
code_pred [random_dseq] typing .

(*values [random] 1 "{(\<Gamma>, t, T). \<Gamma> \<turnstile> t : T}"
*)*)

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
sorry

code_pred [random_dseq inductify] matrix sorry


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

definition
  "transpose M = [map (\<lambda> xs. xs ! i) (takeWhile (\<lambda> xs. i < length xs) M). i \<leftarrow> [0 ..< length (M ! 0)]]"

definition
  "inflate upds = foldr (\<lambda> (i, x) upds. upds[i := x]) upds (replicate (length upds) 0)"

definition
  "jad = apsnd transpose o length_permutate o map sparsify"

definition
  "jad_mv v = inflate o split zip o apsnd (map listsum o transpose o map (map (\<lambda> (i, x). v ! i * x)))"
ML {* ML_Context.trace := false *}

lemma "matrix (M::int list list) rs cs \<Longrightarrow> False"
quickcheck[generator = predicate_compile, size = 6]
oops

lemma
  "\<lbrakk> matrix M rs cs ; length v = cs \<rbrakk> \<Longrightarrow> jad_mv v (jad M) = mv M v"
(*quickcheck[generator = predicate_compile]*)
oops

end