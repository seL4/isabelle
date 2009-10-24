theory Predicate_Compile_ex
imports Main Predicate_Compile
begin

inductive even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
    "even 0"
  | "even n \<Longrightarrow> odd (Suc n)"
  | "odd n \<Longrightarrow> even (Suc n)"

code_pred (mode: [], [1]) even .

thm odd.equation
thm even.equation
(*
lemma unit: "unit_case f = (\<lambda>x. f)"
apply (rule ext)
apply (case_tac x)
apply (simp only: unit.cases)
done

lemma "even_1 (Suc (Suc n)) = even_1 n"
thm even.equation(2)
unfolding even.equation(1)[of "Suc (Suc n)"]
unfolding odd.equation
unfolding single_bind
apply simp
apply (simp add: unit)
unfolding bind_single
apply (rule refl)
done
*)
values "{x. even 2}"
values "{x. odd 2}"
values 10 "{n. even n}"
values 10 "{n. odd n}"

inductive append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    "append [] xs xs"
  | "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

code_pred (mode: [1, 2], [3], [2, 3], [1, 3], [1, 2, 3]) append .
thm append.equation

code_pred (inductify_all) (rpred) append .

thm append.equation
thm append.rpred_equation

values "{(ys, xs). append xs ys [0, Suc 0, 2]}"
values "{zs. append [0, Suc 0, 2] [17, 8] zs}"
values "{ys. append [0, Suc 0, 2] ys [0, Suc 0, 2, 17, 0,5]}"

value [code] "Predicate.the (append_1_2 [0::int, 1, 2] [3, 4, 5])"
value [code] "Predicate.the (append_3 ([]::int list))"

subsection {* Tricky case with alternative rules *}
text {* This cannot be handled correctly yet *}
(*
inductive append2
where
  "append2 [] xs xs"
| "append2 xs ys zs \<Longrightarrow> append2 (x # xs) ys (x # zs)"

lemma append2_Nil: "append2 [] (xs::'b list) xs"
  by (simp add: append2.intros(1))

lemmas [code_pred_intros] = append2_Nil append2.intros(2)

code_pred append2
proof -
  case append2
  from append2.cases[OF append2(1)] append2(2-3) show thesis by blast
qed
*)
subsection {* Tricky cases with tuples *}

inductive tupled_append :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append ([], xs, xs)"
| "tupled_append (xs, ys, zs) \<Longrightarrow> tupled_append (x # xs, ys, x # zs)"

code_pred tupled_append .

thm tupled_append.equation
(*
TODO: values with tupled modes
values "{xs. tupled_append ([1,2,3], [4,5], xs)}"
*)

inductive tupled_append'
where
"tupled_append' ([], xs, xs)"
| "[| ys = fst (xa, y); x # zs = snd (xa, y);
 tupled_append' (xs, ys, x # zs) |] ==> tupled_append' (x # xs, xa, y)"

code_pred (inductify_all) tupled_append' .
thm tupled_append'.equation
(* TODO: Modeanalysis returns mode [2] ?? *)

inductive tupled_append'' :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append'' ([], xs, xs)"
| "ys = fst yszs ==> x # zs = snd yszs ==> tupled_append'' (xs, ys, x # zs) \<Longrightarrow> tupled_append'' (x # xs, yszs)"

thm tupled_append''.cases

code_pred (inductify_all) tupled_append'' .
thm tupled_append''.equation
(* TODO: Modeanalysis returns mode [2] ?? *)

inductive tupled_append''' :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append''' ([], xs, xs)"
| "yszs = (ys, zs) ==> tupled_append''' (xs, yszs) \<Longrightarrow> tupled_append''' (x # xs, ys, x # zs)"

code_pred (inductify_all) tupled_append''' .
thm tupled_append'''.equation
(* TODO: Missing a few modes *)

inductive map_ofP :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "map_ofP ((a, b)#xs) a b"
| "map_ofP xs a b \<Longrightarrow> map_ofP (x#xs) a b"

code_pred map_ofP .
thm map_ofP.equation
section {* reverse *}

inductive rev where
    "rev [] []"
  | "rev xs xs' ==> append xs' [x] ys ==> rev (x#xs) ys"

code_pred rev .

thm rev.equation

values "{xs. rev [0, 1, 2, 3::nat] xs}"

inductive tupled_rev where
  "tupled_rev ([], [])"
| "tupled_rev (xs, xs') \<Longrightarrow> tupled_append (xs', [x], ys) \<Longrightarrow> tupled_rev (x#xs, ys)"

code_pred tupled_rev .
thm tupled_rev.equation

inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

code_pred partition .

inductive tupled_partition :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<times> 'a list \<times> 'a list) \<Rightarrow> bool"
  for f where
   "tupled_partition f ([], [], [])"
  | "f x \<Longrightarrow> tupled_partition f (xs, ys, zs) \<Longrightarrow> tupled_partition f (x # xs, x # ys, zs)"
  | "\<not> f x \<Longrightarrow> tupled_partition f (xs, ys, zs) \<Longrightarrow> tupled_partition f (x # xs, ys, x # zs)"

code_pred tupled_partition .

thm tupled_partition.equation

inductive member
for xs
where "x \<in> set xs ==> member xs x"

lemma [code_pred_intros]:
  "member (x#xs') x"
by (auto intro: member.intros)

lemma [code_pred_intros]:
"member xs x ==> member (x'#xs) x"
by (auto intro: member.intros elim!: member.cases)
(* strange bug must be repaired! *)
(*
code_pred member sorry
*)
inductive is_even :: "nat \<Rightarrow> bool"
where
  "n mod 2 = 0 \<Longrightarrow> is_even n"

code_pred is_even .

values 10 "{(ys, zs). partition is_even
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}"
values 10 "{zs. partition is_even zs [0, 2] [3, 5]}"
values 10 "{zs. partition is_even zs [0, 7] [3, 5]}"

lemma [code_pred_intros]:
  "r a b \<Longrightarrow> tranclp r a b"
  "r a b \<Longrightarrow> tranclp r b c \<Longrightarrow> tranclp r a c"
  by auto

code_pred tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed
(*
code_pred (inductify_all) (rpred) tranclp .
thm tranclp.equation
thm tranclp.rpred_equation
*)

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred succ .

thm succ.equation

values 10 "{(m, n). succ n m}"
values "{m. succ 0 m}"
values "{m. succ m 0}"

(* FIXME: why does this not terminate? -- value chooses mode [] --> [1] and then starts enumerating all successors *)

(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

subsection{* *}

subsection{* IMP *}

types
  var = nat
  state = "int list"

datatype com =
  Skip |
  Ass var "state => int" |
  Seq com com |
  IF "state => bool" com com |
  While "state => bool" com

inductive exec :: "com => state => state => bool" where
"exec Skip s s" |
"exec (Ass x e) s (s[x := e(s)])" |
"exec c1 s1 s2 ==> exec c2 s2 s3 ==> exec (Seq c1 c2) s1 s3" |
"b s ==> exec c1 s t ==> exec (IF b c1 c2) s t" |
"~b s ==> exec c2 s t ==> exec (IF b c1 c2) s t" |
"~b s ==> exec (While b c) s s" |
"b s1 ==> exec c s1 s2 ==> exec (While b c) s2 s3 ==> exec (While b c) s1 s3"

code_pred exec .

values "{t. exec
 (While (%s. s!0 > 0) (Seq (Ass 0 (%s. s!0 - 1)) (Ass 1 (%s. s!1 + 1))))
 [3,5] t}"

inductive tupled_exec :: "(com \<times> state \<times> state) \<Rightarrow> bool" where
"tupled_exec (Skip, s, s)" |
"tupled_exec (Ass x e, s, s[x := e(s)])" |
"tupled_exec (c1, s1, s2) ==> tupled_exec (c2, s2, s3) ==> tupled_exec (Seq c1 c2, s1, s3)" |
"b s ==> tupled_exec (c1, s, t) ==> tupled_exec (IF b c1 c2, s, t)" |
"~b s ==> tupled_exec (c2, s, t) ==> tupled_exec (IF b c1 c2, s, t)" |
"~b s ==> tupled_exec (While b c, s, s)" |
"b s1 ==> tupled_exec (c, s1, s2) ==> tupled_exec (While b c, s2, s3) ==> tupled_exec (While b c, s1, s3)"

code_pred tupled_exec .

subsection{* CCS *}

text{* This example formalizes finite CCS processes without communication or
recursion. For simplicity, labels are natural numbers. *}

datatype proc = nil | pre nat proc | or proc proc | par proc proc

inductive step :: "proc \<Rightarrow> nat \<Rightarrow> proc \<Rightarrow> bool" where
"step (pre n p) n p" |
"step p1 a q \<Longrightarrow> step (or p1 p2) a q" |
"step p2 a q \<Longrightarrow> step (or p1 p2) a q" |
"step p1 a q \<Longrightarrow> step (par p1 p2) a (par q p2)" |
"step p2 a q \<Longrightarrow> step (par p1 p2) a (par p1 q)"

code_pred step .

inductive steps where
"steps p [] p" |
"step p a q \<Longrightarrow> steps q as r \<Longrightarrow> steps p (a#as) r"

code_pred steps .

values 5
 "{as . steps (par (or (pre 0 nil) (pre 1 nil)) (pre 2 nil)) as (par nil nil)}"

(* FIXME
values 3 "{(a,q). step (par nil nil) a q}"
*)

inductive tupled_step :: "(proc \<times> nat \<times> proc) \<Rightarrow> bool"
where
"tupled_step (pre n p, n, p)" |
"tupled_step (p1, a, q) \<Longrightarrow> tupled_step (or p1 p2, a, q)" |
"tupled_step (p2, a, q) \<Longrightarrow> tupled_step (or p1 p2, a, q)" |
"tupled_step (p1, a, q) \<Longrightarrow> tupled_step (par p1 p2, a, par q p2)" |
"tupled_step (p2, a, q) \<Longrightarrow> tupled_step (par p1 p2, a, par p1 q)"

code_pred tupled_step .
thm tupled_step.equation

subsection {* divmod *}

inductive divmod_rel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
    "k < l \<Longrightarrow> divmod_rel k l 0 k"
  | "k \<ge> l \<Longrightarrow> divmod_rel (k - l) l q r \<Longrightarrow> divmod_rel k l (Suc q) r"

code_pred divmod_rel ..

value [code] "Predicate.the (divmod_rel_1_2 1705 42)"

section {* Executing definitions *}

definition Min
where "Min s r x \<equiv> s x \<and> (\<forall>y. r x y \<longrightarrow> x = y)"

code_pred (inductify_all) Min .

subsection {* Examples with lists *}

inductive filterP for Pa where
"(filterP::('a => bool) => 'a list => 'a list => bool) (Pa::'a => bool) [] []"
| "[| (res::'a list) = (y::'a) # (resa::'a list); (filterP::('a => bool) => 'a list => 'a list => bool) (Pa::'a => bool) (xt::'a list) resa; Pa y |]
==> filterP Pa (y # xt) res"
| "[| (filterP::('a => bool) => 'a list => 'a list => bool) (Pa::'a => bool) (xt::'a list) (res::'a list); ~ Pa (y::'a) |] ==> filterP Pa (y # xt) res"

(*
code_pred (inductify_all) (rpred) filterP .
thm filterP.rpred_equation
*)

code_pred (inductify_all) lexord .

thm lexord.equation

lemma "(u, v) : lexord r ==> (x @ u, y @ v) : lexord r"
(*quickcheck[generator=pred_compile]*)
oops

lemmas [code_pred_def] = lexn_conv lex_conv lenlex_conv

code_pred (inductify_all) lexn .
thm lexn.equation

code_pred (inductify_all) lenlex .
thm lenlex.equation
(*
code_pred (inductify_all) (rpred) lenlex .
thm lenlex.rpred_equation
*)
thm lists.intros
code_pred (inductify_all) lists .

thm lists.equation

datatype 'a tree = ET | MKT 'a "'a tree" "'a tree" nat
fun height :: "'a tree => nat" where
"height ET = 0"
| "height (MKT x l r h) = max (height l) (height r) + 1"

consts avl :: "'a tree => bool"
primrec
  "avl ET = True"
  "avl (MKT x l r h) = ((height l = height r \<or> height l = 1 + height r \<or> height r = 1+height l) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

code_pred (inductify_all) avl .
thm avl.equation
(*
lemma [code_pred_inline]: "bot_fun_inst.bot_fun == (\<lambda>(y::'a::type). False)"
unfolding bot_fun_inst.bot_fun[symmetric] bot_bool_eq[symmetric] bot_fun_eq by simp
*)
fun set_of
where
"set_of ET = {}"
| "set_of (MKT n l r h) = insert n (set_of l \<union> set_of r)"

fun is_ord
where
"is_ord ET = True"
| "is_ord (MKT n l r h) =
 ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"
(*
lemma empty_set[code_pred_def]: "{} = (\<lambda>x. False)" unfolding empty_def by simp
thm set_of.simps[unfolded empty_set Un_def]
*)
(*
declare empty_def[code_pred_def]
*)
ML {* prop_of (@{thm set_of.simps(1)}) *}
thm Un_def
thm eq_refl
declare eq_reflection[OF empty_def, code_pred_inline]
thm Un_def
definition Un' where "Un' A B == A Un B"

lemma [code_pred_intros]: "A x ==> Un' A B x"
and  [code_pred_intros] : "B x ==> Un' A B x"
sorry

code_pred Un' sorry

lemmas a = Un'_def[symmetric]
declare a[code_pred_inline]
declare set_of.simps
ML {* prop_of @{thm Un_def} *}
ML {* tap *}
code_pred (inductify_all) set_of .
thm set_of.equation
(* FIXME *)
(*
code_pred (inductify_all) is_ord .
thm is_ord.equation
*)
section {* Definitions about Relations *}

code_pred (inductify_all) converse .
thm converse.equation

code_pred (inductify_all) Domain .
thm Domain.equation

section {* List functions *}

code_pred (inductify_all) length .
thm size_listP.equation

code_pred (inductify_all) concat .
thm concatP.equation

code_pred (inductify_all) hd .
code_pred (inductify_all) tl .
code_pred (inductify_all) last .
code_pred (inductify_all) butlast .
(*code_pred (inductify_all) listsum .*)
code_pred (inductify_all) take .
code_pred (inductify_all) drop .
code_pred (inductify_all) zip .
code_pred (inductify_all) upt .
code_pred set sorry
code_pred (inductify_all) remdups .
code_pred (inductify_all) remove1 .
code_pred (inductify_all) removeAll .
code_pred (inductify_all) distinct .
code_pred (inductify_all) replicate .
code_pred (inductify_all) splice .
code_pred (inductify_all) List.rev .
thm revP.equation

section {* Handling set operations *}



section {* Context Free Grammar *}

datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

code_pred (inductify_all) S\<^isub>1p .

thm S\<^isub>1p.equation

theorem S\<^isub>1_sound:
"w \<in> S\<^isub>1 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=pred_compile]
oops

inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"
(*
code_pred (inductify_all) (rpred) S\<^isub>2 .
ML {* Predicate_Compile_Core.intros_of @{theory} @{const_name "B\<^isub>2"} *}
*)
theorem S\<^isub>2_sound:
"w \<in> S\<^isub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
(*quickcheck[generator=SML]*)
quickcheck[generator=pred_compile, size=15, iterations=100]
oops

inductive_set S\<^isub>3 and A\<^isub>3 and B\<^isub>3 where
  "[] \<in> S\<^isub>3"
| "w \<in> A\<^isub>3 \<Longrightarrow> b # w \<in> S\<^isub>3"
| "w \<in> B\<^isub>3 \<Longrightarrow> a # w \<in> S\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> a # w \<in> A\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> b # w \<in> B\<^isub>3"
| "\<lbrakk>v \<in> B\<^isub>3; w \<in> B\<^isub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>3"

code_pred (inductify_all) S\<^isub>3 .

theorem S\<^isub>3_sound:
"w \<in> S\<^isub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator=pred_compile, size=10, iterations=1]
oops

lemma "\<not> (length w > 2) \<or> \<not> (length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b])"
quickcheck[size=10, generator = pred_compile]
oops

inductive test
where
  "length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] ==> test w"
ML {* @{term "[x \<leftarrow> w. x = a]"} *}
code_pred (inductify_all) test .

thm test.equation
(*
theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>3"
(*quickcheck[generator=SML]*)
quickcheck[generator=pred_compile, size=10, iterations=100]
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

theorem S\<^isub>4_sound:
"w \<in> S\<^isub>4 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
quickcheck[generator = pred_compile, size=2, iterations=1]
oops

theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
quickcheck[generator = pred_compile, size=5, iterations=1]
oops

theorem S\<^isub>4_A\<^isub>4_B\<^isub>4_sound_and_complete:
"w \<in> S\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
"w \<in> A\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] + 1"
"w \<in> B\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = b] = length [x \<leftarrow> w. x = a] + 1"
(*quickcheck[generator = pred_compile, size=5, iterations=1]*)
oops

section {* Lambda *}

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

(*
inductive nth_el' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
where
  "nth_el' (x # xs) 0 x"
| "nth_el' xs i y \<Longrightarrow> nth_el' (x # xs) (Suc i) y"
*)
inductive typing :: "type list \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
  where
    Var [intro!]: "nth_el env x = Some T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "T # env \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs T t : (T \<Rightarrow> U)"
(*  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U" *)
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

lemma "Gamma \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> Gamma \<turnstile> t' : T"
quickcheck[generator = pred_compile, size = 10, iterations = 1000]
oops
(* FIXME *)
(*
inductive test for P where
"[| filter P vs = res |]
==> test P vs res"

code_pred test .
*)
(*
export_code test_for_1_yields_1_2 in SML file -
code_pred (inductify_all) (rpred) test .

thm test.equation
*)

lemma filter_eq_ConsD:
 "filter P ys = x#xs \<Longrightarrow>
  \<exists>us vs. ys = ts @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> xs = filter P vs"
(*quickcheck[generator = pred_compile]*)
oops


end