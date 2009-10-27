theory Predicate_Compile_ex
imports Main Predicate_Compile_Alternative_Defs
begin

subsection {* Basic predicates *}

inductive False' :: "bool"

code_pred (mode: []) False' .
code_pred [depth_limited] False' .
code_pred [rpred] False' .

inductive EmptySet :: "'a \<Rightarrow> bool"

code_pred (mode: [], [1]) EmptySet .

definition EmptySet' :: "'a \<Rightarrow> bool"
where "EmptySet' = {}"

code_pred (mode: [], [1]) [inductify, show_intermediate_results] EmptySet' .

inductive EmptyRel :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

code_pred (mode: [], [1], [2], [1, 2]) EmptyRel .

inductive EmptyClosure :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

code_pred (mode: [], [1], [2], [1, 2])EmptyClosure .
thm EmptyClosure.equation
(* TODO: inductive package is broken!
inductive False'' :: "bool"
where
  "False \<Longrightarrow> False''"

code_pred (mode: []) False'' .

inductive EmptySet'' :: "'a \<Rightarrow> bool"
where
  "False \<Longrightarrow> EmptySet'' x"

code_pred (mode: [1]) EmptySet'' .
code_pred (mode: [], [1]) [inductify] EmptySet'' .
*)
inductive True' :: "bool"
where
  "True \<Longrightarrow> True'"

code_pred (mode: []) True' .

consts a' :: 'a

inductive Fact :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
"Fact a' a'"

code_pred (mode: [], [1], [2], [1, 2]) Fact .

inductive zerozero :: "nat * nat => bool"
where
  "zerozero (0, 0)"

code_pred zerozero .
code_pred [rpred, show_compilation] zerozero .

subsection {* Preprocessor Inlining  *}

definition "equals == (op =)"
 
inductive zerozero' where
  "equals (x, y) (0, 0) ==> zerozero' (x, y)"

code_pred (mode: [1]) zerozero' .

lemma zerozero'_eq: "zerozero' == zerozero"
proof -
  have "zerozero' = zerozero"
    apply (auto simp add: mem_def)
    apply (cases rule: zerozero'.cases)
    apply (auto simp add: equals_def intro: zerozero.intros)
    apply (cases rule: zerozero.cases)
    apply (auto simp add: equals_def intro: zerozero'.intros)
    done
  from this show "zerozero' == zerozero" by auto
qed

declare zerozero'_eq [code_pred_inline]

definition "zerozero'' x == zerozero' x"

text {* if preprocessing fails, zerozero'' will not have all modes. *}
ML {* Predicate_Compile_Inline_Defs.get @{context} *}
(* TODO: *)
code_pred (mode: [1]) [inductify, show_intermediate_results] zerozero'' .

subsection {* even predicate *}

inductive even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
    "even 0"
  | "even n \<Longrightarrow> odd (Suc n)"
  | "odd n \<Longrightarrow> even (Suc n)"

code_pred (mode: [], [1]) even .
code_pred [depth_limited] even .
code_pred [rpred] even .

thm odd.equation
thm even.equation
thm odd.depth_limited_equation
thm even.depth_limited_equation
thm even.rpred_equation
thm odd.rpred_equation

values "{x. even 2}"
values "{x. odd 2}"
values 10 "{n. even n}"
values 10 "{n. odd n}"
values [depth_limit = 2] "{x. even 6}"
values [depth_limit = 7] "{x. even 6}"
values [depth_limit = 2] "{x. odd 7}"
values [depth_limit = 8] "{x. odd 7}"
values [depth_limit = 7] 10 "{n. even n}"

definition odd' where "odd' x == \<not> even x"

code_pred [inductify] odd' .
code_pred [inductify, depth_limited] odd' .
code_pred [inductify, rpred] odd' .

thm odd'.depth_limited_equation
values [depth_limit = 2] "{x. odd' 7}"
values [depth_limit = 9] "{x. odd' 7}"

inductive is_even :: "nat \<Rightarrow> bool"
where
  "n mod 2 = 0 \<Longrightarrow> is_even n"

code_pred is_even .

subsection {* append predicate *}

inductive append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    "append [] xs xs"
  | "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

code_pred (mode: [1, 2], [3], [2, 3], [1, 3], [1, 2, 3]) append .
code_pred [depth_limited] append .
code_pred [rpred] append .

thm append.equation
thm append.depth_limited_equation
thm append.rpred_equation

values "{(ys, xs). append xs ys [0, Suc 0, 2]}"
values "{zs. append [0, Suc 0, 2] [17, 8] zs}"
values "{ys. append [0, Suc 0, 2] ys [0, Suc 0, 2, 17, 0, 5]}"
values [depth_limit = 3] "{(xs, ys). append xs ys [1, 2, 3, 4, (5::nat)]}"
values [random] 15 "{(ys, zs). append [1::nat, 2] ys zs}"

value [code] "Predicate.the (append_1_2 [0::int, 1, 2] [3, 4, 5])"
value [code] "Predicate.the (append_3 ([]::int list))"

text {* tricky case with alternative rules *}

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

inductive tupled_append :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append ([], xs, xs)"
| "tupled_append (xs, ys, zs) \<Longrightarrow> tupled_append (x # xs, ys, x # zs)"

code_pred tupled_append .
code_pred [rpred] tupled_append .
thm tupled_append.equation
(*
TODO: values with tupled modes
values "{xs. tupled_append ([1,2,3], [4,5], xs)}"
*)

inductive tupled_append'
where
"tupled_append' ([], xs, xs)"
| "[| ys = fst (xa, y); x # zs = snd (xa, y);
 tupled_append' (xs, ys, zs) |] ==> tupled_append' (x # xs, xa, y)"

code_pred tupled_append' .
thm tupled_append'.equation

inductive tupled_append'' :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append'' ([], xs, xs)"
| "ys = fst yszs ==> x # zs = snd yszs ==> tupled_append'' (xs, ys, zs) \<Longrightarrow> tupled_append'' (x # xs, yszs)"

thm tupled_append''.cases

code_pred [inductify] tupled_append'' .
thm tupled_append''.equation

inductive tupled_append''' :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append''' ([], xs, xs)"
| "yszs = (ys, zs) ==> tupled_append''' (xs, yszs) \<Longrightarrow> tupled_append''' (x # xs, ys, x # zs)"

code_pred [inductify] tupled_append''' .
thm tupled_append'''.equation

subsection {* map_ofP predicate *}

inductive map_ofP :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "map_ofP ((a, b)#xs) a b"
| "map_ofP xs a b \<Longrightarrow> map_ofP (x#xs) a b"

code_pred (mode: [1], [1, 2], [1, 2, 3], [1, 3]) map_ofP .
thm map_ofP.equation

subsection {* filter predicate *}

inductive filter1
for P
where
  "filter1 P [] []"
| "P x ==> filter1 P xs ys ==> filter1 P (x#xs) (x#ys)"
| "\<not> P x ==> filter1 P xs ys ==> filter1 P (x#xs) ys"

code_pred (mode: [1], [1, 2]) filter1 .
code_pred [depth_limited] filter1 .
code_pred [rpred] filter1 .

thm filter1.equation

inductive filter2
where
  "filter2 P [] []"
| "P x ==> filter2 P xs ys ==> filter2 P (x#xs) (x#ys)"
| "\<not> P x ==> filter2 P xs ys ==> filter2 P (x#xs) ys"

code_pred (mode: [1, 2, 3], [1, 2]) filter2 .
code_pred [depth_limited] filter2 .
code_pred [rpred] filter2 .
thm filter2.equation
thm filter2.rpred_equation

inductive filter3
for P
where
  "List.filter P xs = ys ==> filter3 P xs ys"

code_pred filter3 .
code_pred [depth_limited] filter3 .
thm filter3.depth_limited_equation

inductive filter4
where
  "List.filter P xs = ys ==> filter4 P xs ys"

code_pred filter4 .
code_pred [depth_limited] filter4 .
code_pred [rpred] filter4 .

subsection {* reverse predicate *}

inductive rev where
    "rev [] []"
  | "rev xs xs' ==> append xs' [x] ys ==> rev (x#xs) ys"

code_pred (mode: [1], [2], [1, 2]) rev .

thm rev.equation

values "{xs. rev [0, 1, 2, 3::nat] xs}"

inductive tupled_rev where
  "tupled_rev ([], [])"
| "tupled_rev (xs, xs') \<Longrightarrow> tupled_append (xs', [x], ys) \<Longrightarrow> tupled_rev (x#xs, ys)"

code_pred tupled_rev .
thm tupled_rev.equation

subsection {* partition predicate *}

inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

code_pred (mode: [1], [2, 3], [1, 2], [1, 3], [1, 2, 3]) partition .
code_pred [depth_limited] partition .
code_pred [rpred] partition .

values 10 "{(ys, zs). partition is_even
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}"
values 10 "{zs. partition is_even zs [0, 2] [3, 5]}"
values 10 "{zs. partition is_even zs [0, 7] [3, 5]}"

inductive tupled_partition :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<times> 'a list \<times> 'a list) \<Rightarrow> bool"
  for f where
   "tupled_partition f ([], [], [])"
  | "f x \<Longrightarrow> tupled_partition f (xs, ys, zs) \<Longrightarrow> tupled_partition f (x # xs, x # ys, zs)"
  | "\<not> f x \<Longrightarrow> tupled_partition f (xs, ys, zs) \<Longrightarrow> tupled_partition f (x # xs, ys, x # zs)"

code_pred tupled_partition .

thm tupled_partition.equation

lemma [code_pred_intros]:
  "r a b \<Longrightarrow> tranclp r a b"
  "r a b \<Longrightarrow> tranclp r b c \<Longrightarrow> tranclp r a c"
  by auto

subsection {* transitive predicate *}

code_pred tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed

code_pred [depth_limited] tranclp .
code_pred [rpred] tranclp .
thm tranclp.equation
thm tranclp.rpred_equation

inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred succ .
code_pred [rpred] succ .
thm succ.equation
thm succ.rpred_equation

values 10 "{(m, n). succ n m}"
values "{m. succ 0 m}"
values "{m. succ m 0}"

(* FIXME: why does this not terminate? -- value chooses mode [] --> [1] and then starts enumerating all successors *)

(*
values 20 "{n. tranclp succ 10 n}"
values "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"
*)

subsection {* IMP *}

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

subsection {* CCS *}

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

subsection {* Minimum *}

definition Min
where "Min s r x \<equiv> s x \<and> (\<forall>y. r x y \<longrightarrow> x = y)"

code_pred [inductify] Min .

subsection {* Lexicographic order *}

code_pred [inductify] lexord .
code_pred [inductify, rpred] lexord .
thm lexord.equation
thm lexord.rpred_equation

inductive less_than_nat :: "nat * nat => bool"
where
  "less_than_nat (0, x)"
| "less_than_nat (x, y) ==> less_than_nat (Suc x, Suc y)"
 
code_pred less_than_nat .

code_pred [depth_limited] less_than_nat .
code_pred [rpred] less_than_nat .

inductive test_lexord :: "nat list * nat list => bool"
where
  "lexord less_than_nat (xs, ys) ==> test_lexord (xs, ys)"

code_pred [rpred] test_lexord .
code_pred [depth_limited] test_lexord .
thm test_lexord.depth_limited_equation
thm test_lexord.rpred_equation

values "{x. test_lexord ([1, 2, 3], [1, 2, 5])}"
values [depth_limit = 5] "{x. test_lexord ([1, 2, 3], [1, 2, 5])}"

lemmas [code_pred_def] = lexn_conv lex_conv lenlex_conv

code_pred [inductify] lexn .
thm lexn.equation

code_pred [rpred] lexn .

thm lexn.rpred_equation

code_pred [inductify, show_steps] lenlex .
thm lenlex.equation

code_pred [inductify, rpred] lenlex .
thm lenlex.rpred_equation

code_pred [inductify] lists .
thm lists.equation

subsection {* AVL Tree *}

datatype 'a tree = ET | MKT 'a "'a tree" "'a tree" nat
fun height :: "'a tree => nat" where
"height ET = 0"
| "height (MKT x l r h) = max (height l) (height r) + 1"

consts avl :: "'a tree => bool"
primrec
  "avl ET = True"
  "avl (MKT x l r h) = ((height l = height r \<or> height l = 1 + height r \<or> height r = 1+height l) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

code_pred [inductify] avl .
thm avl.equation

code_pred [rpred] avl .
thm avl.rpred_equation

fun set_of
where
"set_of ET = {}"
| "set_of (MKT n l r h) = insert n (set_of l \<union> set_of r)"

fun is_ord :: "nat tree => bool"
where
"is_ord ET = True"
| "is_ord (MKT n l r h) =
 ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"

code_pred (mode: [1], [1, 2]) [inductify] set_of .
thm set_of.equation

code_pred [inductify] is_ord .
thm is_ord.equation


subsection {* Definitions about Relations *}

code_pred [inductify] converse .
thm converse.equation
code_pred [inductify] rel_comp .
thm rel_comp.equation
code_pred [inductify] Image .
thm Image.equation
(*TODO: *)

declare Id_on_def[unfolded UNION_def, code_pred_def]

code_pred [inductify] Id_on .
thm Id_on.equation
code_pred [inductify] Domain .
thm Domain.equation
code_pred [inductify] Range .
thm Range.equation
code_pred [inductify] Field .
declare Sigma_def[unfolded UNION_def, code_pred_def]
declare refl_on_def[unfolded UNION_def, code_pred_def]
code_pred [inductify] refl_on .
thm refl_on.equation
code_pred [inductify] total_on .
thm total_on.equation
code_pred [inductify] antisym .
thm antisym.equation
code_pred [inductify] trans .
thm trans.equation
code_pred [inductify] single_valued .
thm single_valued.equation
code_pred [inductify] inv_image .
thm inv_image.equation

subsection {* Inverting list functions *}

code_pred [inductify] length .
code_pred [inductify, rpred] length .
thm size_listP.equation
thm size_listP.rpred_equation

values [random] 20 "{xs. size_listP (xs::nat list) (5::nat)}"

code_pred [inductify] concat .
code_pred [inductify] hd .
code_pred [inductify] tl .
code_pred [inductify] last .
code_pred [inductify] butlast .
code_pred [inductify] take .
code_pred [inductify] drop .
code_pred [inductify] zip .
code_pred [inductify] upt .
code_pred [inductify] remdups .
code_pred [inductify] remove1 .
code_pred [inductify] removeAll .
code_pred [inductify] distinct .
code_pred [inductify] replicate .
code_pred [inductify] splice .
code_pred [inductify] List.rev .
code_pred [inductify] map .
code_pred [inductify] foldr .
code_pred [inductify] foldl .
code_pred [inductify] filter .
code_pred [inductify, rpred] filter .

subsection {* Context Free Grammar *}

datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

code_pred [inductify] S\<^isub>1p .
code_pred [inductify, rpred] S\<^isub>1p .
thm S\<^isub>1p.equation
thm S\<^isub>1p.rpred_equation

values [random] 5 "{x. S\<^isub>1p x}"

inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"

code_pred [inductify, rpred] S\<^isub>2 .
thm S\<^isub>2.rpred_equation
thm A\<^isub>2.rpred_equation
thm B\<^isub>2.rpred_equation

values [random] 10 "{x. S\<^isub>2 x}"

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

inductive_set S\<^isub>4 and A\<^isub>4 and B\<^isub>4 where
  "[] \<in> S\<^isub>4"
| "w \<in> A\<^isub>4 \<Longrightarrow> b # w \<in> S\<^isub>4"
| "w \<in> B\<^isub>4 \<Longrightarrow> a # w \<in> S\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> a # w \<in> A\<^isub>4"
| "\<lbrakk>v \<in> A\<^isub>4; w \<in> A\<^isub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> b # w \<in> B\<^isub>4"
| "\<lbrakk>v \<in> B\<^isub>4; w \<in> B\<^isub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>4"

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
  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

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

end