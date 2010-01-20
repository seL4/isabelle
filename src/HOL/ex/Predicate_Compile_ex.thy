theory Predicate_Compile_ex
imports Predicate_Compile_Alternative_Defs
begin

subsection {* Basic predicates *}

inductive False' :: "bool"

code_pred (expected_modes: bool) False' .
code_pred [dseq] False' .
code_pred [random_dseq] False' .

values [expected "{}" pred] "{x. False'}"
values [expected "{}" dseq 1] "{x. False'}"
values [expected "{}" random_dseq 1, 1, 1] "{x. False'}"

value "False'"


inductive True' :: "bool"
where
  "True ==> True'"

code_pred True' .
code_pred [dseq] True' .
code_pred [random_dseq] True' .

thm True'.equation
thm True'.dseq_equation
thm True'.random_dseq_equation
values [expected "{()}" ]"{x. True'}"
values [expected "{}" dseq 0] "{x. True'}"
values [expected "{()}" dseq 1] "{x. True'}"
values [expected "{()}" dseq 2] "{x. True'}"
values [expected "{}" random_dseq 1, 1, 0] "{x. True'}"
values [expected "{}" random_dseq 1, 1, 1] "{x. True'}"
values [expected "{()}" random_dseq 1, 1, 2] "{x. True'}"
values [expected "{()}" random_dseq 1, 1, 3] "{x. True'}"

inductive EmptySet :: "'a \<Rightarrow> bool"

code_pred (expected_modes: o => bool, i => bool) EmptySet .

definition EmptySet' :: "'a \<Rightarrow> bool"
where "EmptySet' = {}"

code_pred (expected_modes: o => bool, i => bool) [inductify] EmptySet' .

inductive EmptyRel :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

code_pred (expected_modes: o => o => bool, i => o => bool, o => i => bool, i => i => bool) EmptyRel .

inductive EmptyClosure :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

code_pred
  (expected_modes: (o => o => bool) => o => o => bool, (o => o => bool) => i => o => bool,
         (o => o => bool) => o => i => bool, (o => o => bool) => i => i => bool,
         (i => o => bool) => o => o => bool, (i => o => bool) => i => o => bool,
         (i => o => bool) => o => i => bool, (i => o => bool) => i => i => bool,
         (o => i => bool) => o => o => bool, (o => i => bool) => i => o => bool,
         (o => i => bool) => o => i => bool, (o => i => bool) => i => i => bool,
         (i => i => bool) => o => o => bool, (i => i => bool) => i => o => bool,
         (i => i => bool) => o => i => bool, (i => i => bool) => i => i => bool)
  EmptyClosure .

thm EmptyClosure.equation

(* TODO: inductive package is broken!
inductive False'' :: "bool"
where
  "False \<Longrightarrow> False''"

code_pred (expected_modes: []) False'' .

inductive EmptySet'' :: "'a \<Rightarrow> bool"
where
  "False \<Longrightarrow> EmptySet'' x"

code_pred (expected_modes: [1]) EmptySet'' .
code_pred (expected_modes: [], [1]) [inductify] EmptySet'' .
*)

consts a' :: 'a

inductive Fact :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
"Fact a' a'"

code_pred (expected_modes: o => o => bool, i => o => bool, o => i => bool, i => i => bool) Fact .

inductive zerozero :: "nat * nat => bool"
where
  "zerozero (0, 0)"

code_pred (expected_modes: i => bool, i * o => bool, o * i => bool, o => bool) zerozero .
code_pred [dseq] zerozero .
code_pred [random_dseq] zerozero .

thm zerozero.equation
thm zerozero.dseq_equation
thm zerozero.random_dseq_equation

text {* We expect the user to expand the tuples in the values command.
The following values command is not supported. *}
(*values "{x. zerozero x}" *)
text {* Instead, the user must type *}
values "{(x, y). zerozero (x, y)}"

values [expected "{}" dseq 0] "{(x, y). zerozero (x, y)}"
values [expected "{(0::nat, 0::nat)}" dseq 1] "{(x, y). zerozero (x, y)}"
values [expected "{(0::nat, 0::nat)}" dseq 2] "{(x, y). zerozero (x, y)}"
values [expected "{}" random_dseq 1, 1, 2] "{(x, y). zerozero (x, y)}"
values [expected "{(0::nat, 0:: nat)}" random_dseq 1, 1, 3] "{(x, y). zerozero (x, y)}"

inductive nested_tuples :: "((int * int) * int * int) => bool"
where
  "nested_tuples ((0, 1), 2, 3)"

code_pred nested_tuples .

inductive JamesBond :: "nat => int => code_numeral => bool"
where
  "JamesBond 0 0 7"

code_pred JamesBond .

values [expected "{(0::nat, 0::int , 7::code_numeral)}"] "{(a, b, c). JamesBond a b c}"
values [expected "{(0::nat, 7::code_numeral, 0:: int)}"] "{(a, c, b). JamesBond a b c}"
values [expected "{(0::int, 0::nat, 7::code_numeral)}"] "{(b, a, c). JamesBond a b c}"
values [expected "{(0::int, 7::code_numeral, 0::nat)}"] "{(b, c, a). JamesBond a b c}"
values [expected "{(7::code_numeral, 0::nat, 0::int)}"] "{(c, a, b). JamesBond a b c}"
values [expected "{(7::code_numeral, 0::int, 0::nat)}"] "{(c, b, a). JamesBond a b c}"

values [expected "{(7::code_numeral, 0::int)}"] "{(a, b). JamesBond 0 b a}"
values [expected "{(7::code_numeral, 0::nat)}"] "{(c, a). JamesBond a 0 c}"
values [expected "{(0::nat, 7::code_numeral)}"] "{(a, c). JamesBond a 0 c}"


subsection {* Alternative Rules *}

datatype char = C | D | E | F | G | H

inductive is_C_or_D
where
  "(x = C) \<or> (x = D) ==> is_C_or_D x"

code_pred (expected_modes: i => bool) is_C_or_D .
thm is_C_or_D.equation

inductive is_D_or_E
where
  "(x = D) \<or> (x = E) ==> is_D_or_E x"

lemma [code_pred_intro]:
  "is_D_or_E D"
by (auto intro: is_D_or_E.intros)

lemma [code_pred_intro]:
  "is_D_or_E E"
by (auto intro: is_D_or_E.intros)

code_pred (expected_modes: o => bool, i => bool) is_D_or_E
proof -
  case is_D_or_E
  from this(1) show thesis
  proof
    fix xa
    assume x: "x = xa"
    assume "xa = D \<or> xa = E"
    from this show thesis
    proof
      assume "xa = D" from this x is_D_or_E(2) show thesis by simp
    next
      assume "xa = E" from this x is_D_or_E(3) show thesis by simp
    qed
  qed
qed

thm is_D_or_E.equation

inductive is_F_or_G
where
  "x = F \<or> x = G ==> is_F_or_G x"

lemma [code_pred_intro]:
  "is_F_or_G F"
by (auto intro: is_F_or_G.intros)

lemma [code_pred_intro]:
  "is_F_or_G G"
by (auto intro: is_F_or_G.intros)

inductive is_FGH
where
  "is_F_or_G x ==> is_FGH x"
| "is_FGH H"

text {* Compilation of is_FGH requires elimination rule for is_F_or_G *}

code_pred (expected_modes: o => bool, i => bool) is_FGH
proof -
  case is_F_or_G
  from this(1) show thesis
  proof
    fix xa
    assume x: "x = xa"
    assume "xa = F \<or> xa = G"
    from this show thesis
    proof
      assume "xa = F"
      from this x is_F_or_G(2) show thesis by simp
    next
      assume "xa = G"
      from this x is_F_or_G(3) show thesis by simp
    qed
  qed
qed

subsection {* Preprocessor Inlining  *}

definition "equals == (op =)"
 
inductive zerozero' :: "nat * nat => bool" where
  "equals (x, y) (0, 0) ==> zerozero' (x, y)"

code_pred (expected_modes: i => bool) zerozero' .

lemma zerozero'_eq: "zerozero' x == zerozero x"
proof -
  have "zerozero' = zerozero"
    apply (auto simp add: mem_def)
    apply (cases rule: zerozero'.cases)
    apply (auto simp add: equals_def intro: zerozero.intros)
    apply (cases rule: zerozero.cases)
    apply (auto simp add: equals_def intro: zerozero'.intros)
    done
  from this show "zerozero' x == zerozero x" by auto
qed

declare zerozero'_eq [code_pred_inline]

definition "zerozero'' x == zerozero' x"

text {* if preprocessing fails, zerozero'' will not have all modes. *}

code_pred (expected_modes: i * i => bool, i * o => bool, o * i => bool, o => bool) [inductify] zerozero'' .

subsection {* Sets and Numerals *}

definition
  "one_or_two = {Suc 0, (Suc (Suc 0))}"

code_pred [inductify] one_or_two .
code_pred [dseq] one_or_two .
(*code_pred [random_dseq] one_or_two .*)
values [expected "{Suc 0::nat, 2::nat}"] "{x. one_or_two x}"
(*values [random_dseq 1,1,2] "{x. one_or_two x}"*)

inductive one_or_two' :: "nat => bool"
where
  "one_or_two' 1"
| "one_or_two' 2"

code_pred one_or_two' .
thm one_or_two'.equation

values "{x. one_or_two' x}"

definition one_or_two'':
  "one_or_two'' == {1, (2::nat)}"
ML {* prop_of @{thm one_or_two''} *}
(*code_pred [inductify] one_or_two'' .
thm one_or_two''.equation

values "{x. one_or_two'' x}"
*)
subsection {* even predicate *}

inductive even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
    "even 0"
  | "even n \<Longrightarrow> odd (Suc n)"
  | "odd n \<Longrightarrow> even (Suc n)"

code_pred (expected_modes: i => bool, o => bool) even .
code_pred [dseq] even .
code_pred [random_dseq] even .

thm odd.equation
thm even.equation
thm odd.dseq_equation
thm even.dseq_equation
thm odd.random_dseq_equation
thm even.random_dseq_equation

values "{x. even 2}"
values "{x. odd 2}"
values 10 "{n. even n}"
values 10 "{n. odd n}"
values [expected "{}" dseq 2] "{x. even 6}"
values [expected "{}" dseq 6] "{x. even 6}"
values [expected "{()}" dseq 7] "{x. even 6}"
values [dseq 2] "{x. odd 7}"
values [dseq 6] "{x. odd 7}"
values [dseq 7] "{x. odd 7}"
values [expected "{()}" dseq 8] "{x. odd 7}"

values [expected "{}" dseq 0] 8 "{x. even x}"
values [expected "{0::nat}" dseq 1] 8 "{x. even x}"
values [expected "{0::nat, 2}" dseq 3] 8 "{x. even x}"
values [expected "{0::nat, 2}" dseq 4] 8 "{x. even x}"
values [expected "{0::nat, 2, 4}" dseq 6] 8 "{x. even x}"

values [random_dseq 1, 1, 0] 8 "{x. even x}"
values [random_dseq 1, 1, 1] 8 "{x. even x}"
values [random_dseq 1, 1, 2] 8 "{x. even x}"
values [random_dseq 1, 1, 3] 8 "{x. even x}"
values [random_dseq 1, 1, 6] 8 "{x. even x}"

values [expected "{}" random_dseq 1, 1, 7] "{x. odd 7}"
values [random_dseq 1, 1, 8] "{x. odd 7}"
values [random_dseq 1, 1, 9] "{x. odd 7}"

definition odd' where "odd' x == \<not> even x"

code_pred (expected_modes: i => bool) [inductify] odd' .
code_pred [dseq inductify] odd' .
code_pred [random_dseq inductify] odd' .

values [expected "{}" dseq 2] "{x. odd' 7}"
values [expected "{()}" dseq 9] "{x. odd' 7}"
values [expected "{}" dseq 2] "{x. odd' 8}"
values [expected "{}" dseq 10] "{x. odd' 8}"


inductive is_even :: "nat \<Rightarrow> bool"
where
  "n mod 2 = 0 \<Longrightarrow> is_even n"

code_pred (expected_modes: i => bool) is_even .

subsection {* append predicate *}

inductive append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    "append [] xs xs"
  | "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

code_pred (modes: i => i => o => bool as "concat", o => o => i => bool as "slice", o => i => i => bool as prefix,
  i => o => i => bool as suffix, i => i => i => bool) append .
code_pred [dseq] append .
code_pred [random_dseq] append .

thm append.equation
thm append.dseq_equation
thm append.random_dseq_equation

values "{(ys, xs). append xs ys [0, Suc 0, 2]}"
values "{zs. append [0, Suc 0, 2] [17, 8] zs}"
values "{ys. append [0, Suc 0, 2] ys [0, Suc 0, 2, 17, 0, 5]}"

values [expected "{}" dseq 0] 10 "{(xs, ys). append xs ys [1, 2, 3, 4, (5::nat)]}"
values [expected "{(([]::nat list), [Suc 0, 2, 3, 4, (5::nat)])}" dseq 1] 10 "{(xs, ys). append xs ys [1, 2, 3, 4, (5::nat)]}"
values [dseq 4] 10 "{(xs, ys). append xs ys [1, 2, 3, 4, (5::nat)]}"
values [dseq 6] 10 "{(xs, ys). append xs ys [1, 2, 3, 4, (5::nat)]}"
values [random_dseq 1, 1, 4] 10 "{(xs, ys). append xs ys [1, 2, 3, 4, (5::nat)]}"
values [random_dseq 1, 1, 1] 10 "{(xs, ys, zs::int list). append xs ys zs}"
values [random_dseq 1, 1, 3] 10 "{(xs, ys, zs::int list). append xs ys zs}"
values [random_dseq 3, 1, 3] 10 "{(xs, ys, zs::int list). append xs ys zs}"
values [random_dseq 1, 3, 3] 10 "{(xs, ys, zs::int list). append xs ys zs}"
values [random_dseq 1, 1, 4] 10 "{(xs, ys, zs::int list). append xs ys zs}"

value [code] "Predicate.the (concat [0::int, 1, 2] [3, 4, 5])"
value [code] "Predicate.the (slice ([]::int list))"


text {* tricky case with alternative rules *}

inductive append2
where
  "append2 [] xs xs"
| "append2 xs ys zs \<Longrightarrow> append2 (x # xs) ys (x # zs)"

lemma append2_Nil: "append2 [] (xs::'b list) xs"
  by (simp add: append2.intros(1))

lemmas [code_pred_intro] = append2_Nil append2.intros(2)

code_pred (expected_modes: i => i => o => bool, o => o => i => bool, o => i => i => bool,
  i => o => i => bool, i => i => i => bool) append2
proof -
  case append2
  from append2(1) show thesis
  proof
    fix xs
    assume "xa = []" "xb = xs" "xc = xs"
    from this append2(2) show thesis by simp
  next
    fix xs ys zs x
    assume "xa = x # xs" "xb = ys" "xc = x # zs" "append2 xs ys zs"
    from this append2(3) show thesis by fastsimp
  qed
qed

inductive tupled_append :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append ([], xs, xs)"
| "tupled_append (xs, ys, zs) \<Longrightarrow> tupled_append (x # xs, ys, x # zs)"

code_pred (expected_modes: i * i * o => bool, o * o * i => bool, o * i * i => bool,
  i * o * i => bool, i * i * i => bool) tupled_append .
code_pred [random_dseq] tupled_append .
thm tupled_append.equation

values "{xs. tupled_append ([(1::nat), 2, 3], [4, 5], xs)}"

inductive tupled_append'
where
"tupled_append' ([], xs, xs)"
| "[| ys = fst (xa, y); x # zs = snd (xa, y);
 tupled_append' (xs, ys, zs) |] ==> tupled_append' (x # xs, xa, y)"

code_pred (expected_modes: i * i * o => bool, o * o * i => bool, o * i * i => bool,
  i * o * i => bool, i * i * i => bool) tupled_append' .
thm tupled_append'.equation

inductive tupled_append'' :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append'' ([], xs, xs)"
| "ys = fst yszs ==> x # zs = snd yszs ==> tupled_append'' (xs, ys, zs) \<Longrightarrow> tupled_append'' (x # xs, yszs)"

code_pred (expected_modes: i * i * o => bool, o * o * i => bool, o * i * i => bool,
  i * o * i => bool, i * i * i => bool) tupled_append'' .
thm tupled_append''.equation

inductive tupled_append''' :: "'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool"
where
  "tupled_append''' ([], xs, xs)"
| "yszs = (ys, zs) ==> tupled_append''' (xs, yszs) \<Longrightarrow> tupled_append''' (x # xs, ys, x # zs)"

code_pred (expected_modes: i * i * o => bool, o * o * i => bool, o * i * i => bool,
  i * o * i => bool, i * i * i => bool) tupled_append''' .
thm tupled_append'''.equation

subsection {* map_ofP predicate *}

inductive map_ofP :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "map_ofP ((a, b)#xs) a b"
| "map_ofP xs a b \<Longrightarrow> map_ofP (x#xs) a b"

code_pred (expected_modes: i => o => o => bool, i => i => o => bool, i => o => i => bool, i => i => i => bool) map_ofP .
thm map_ofP.equation

subsection {* filter predicate *}

inductive filter1
for P
where
  "filter1 P [] []"
| "P x ==> filter1 P xs ys ==> filter1 P (x#xs) (x#ys)"
| "\<not> P x ==> filter1 P xs ys ==> filter1 P (x#xs) ys"

code_pred (expected_modes: (i => bool) => i => o => bool, (i => bool) => i => i => bool) filter1 .
code_pred [dseq] filter1 .
code_pred [random_dseq] filter1 .

thm filter1.equation

values [expected "{[0::nat, 2, 4]}"] "{xs. filter1 even [0, 1, 2, 3, 4] xs}"
values [expected "{}" dseq 9] "{xs. filter1 even [0, 1, 2, 3, 4] xs}"
values [expected "{[0::nat, 2, 4]}" dseq 10] "{xs. filter1 even [0, 1, 2, 3, 4] xs}"

inductive filter2
where
  "filter2 P [] []"
| "P x ==> filter2 P xs ys ==> filter2 P (x#xs) (x#ys)"
| "\<not> P x ==> filter2 P xs ys ==> filter2 P (x#xs) ys"

code_pred (expected_modes: (i => bool) => i => i => bool, (i => bool) => i => o => bool) filter2 .
code_pred [dseq] filter2 .
code_pred [random_dseq] filter2 .

thm filter2.equation
thm filter2.random_dseq_equation

(*
inductive filter3
for P
where
  "List.filter P xs = ys ==> filter3 P xs ys"

code_pred (expected_modes: (o => bool) => i => o => bool, (o => bool) => i => i => bool , (i => bool) => i => o => bool, (i => bool) => i => i => bool) [skip_proof] filter3 .

code_pred [dseq] filter3 .
thm filter3.dseq_equation
*)
inductive filter4
where
  "List.filter P xs = ys ==> filter4 P xs ys"

(*code_pred (expected_modes: i => i => o => bool, i => i => i => bool) filter4 .*)
(*code_pred [depth_limited] filter4 .*)
(*code_pred [random] filter4 .*)

subsection {* reverse predicate *}

inductive rev where
    "rev [] []"
  | "rev xs xs' ==> append xs' [x] ys ==> rev (x#xs) ys"

code_pred (expected_modes: i => o => bool, o => i => bool, i => i => bool) rev .

thm rev.equation

values "{xs. rev [0, 1, 2, 3::nat] xs}"

inductive tupled_rev where
  "tupled_rev ([], [])"
| "tupled_rev (xs, xs') \<Longrightarrow> tupled_append (xs', [x], ys) \<Longrightarrow> tupled_rev (x#xs, ys)"

code_pred (expected_modes: i * o => bool, o * i => bool, i * i => bool) tupled_rev .
thm tupled_rev.equation

subsection {* partition predicate *}

inductive partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for f where
    "partition f [] [] []"
  | "f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) (x # ys) zs"
  | "\<not> f x \<Longrightarrow> partition f xs ys zs \<Longrightarrow> partition f (x # xs) ys (x # zs)"

code_pred (expected_modes: (i => bool) => i => o => o => bool, (i => bool) => o => i => i => bool,
  (i => bool) => i => i => o => bool, (i => bool) => i => o => i => bool, (i => bool) => i => i => i => bool)
  partition .
code_pred [dseq] partition .
code_pred [random_dseq] partition .

values 10 "{(ys, zs). partition is_even
  [0, Suc 0, 2, 3, 4, 5, 6, 7] ys zs}"
values 10 "{zs. partition is_even zs [0, 2] [3, 5]}"
values 10 "{zs. partition is_even zs [0, 7] [3, 5]}"

inductive tupled_partition :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<times> 'a list \<times> 'a list) \<Rightarrow> bool"
  for f where
   "tupled_partition f ([], [], [])"
  | "f x \<Longrightarrow> tupled_partition f (xs, ys, zs) \<Longrightarrow> tupled_partition f (x # xs, x # ys, zs)"
  | "\<not> f x \<Longrightarrow> tupled_partition f (xs, ys, zs) \<Longrightarrow> tupled_partition f (x # xs, ys, x # zs)"

code_pred (expected_modes: (i => bool) => i => bool, (i => bool) => (i * i * o) => bool, (i => bool) => (i * o * i) => bool,
  (i => bool) => (o * i * i) => bool, (i => bool) => (i * o * o) => bool) tupled_partition .

thm tupled_partition.equation

lemma [code_pred_intro]:
  "r a b \<Longrightarrow> tranclp r a b"
  "r a b \<Longrightarrow> tranclp r b c \<Longrightarrow> tranclp r a c"
  by auto

subsection {* transitive predicate *}

text {* Also look at the tabled transitive closure in the Library *}

code_pred (modes: (i => o => bool) => i => i => bool, (i => o => bool) => i => o => bool as forwards_trancl,
  (o => i => bool) => i => i => bool, (o => i => bool) => o => i => bool as backwards_trancl, (o => o => bool) => i => i => bool, (o => o => bool) => i => o => bool,
  (o => o => bool) => o => i => bool, (o => o => bool) => o => o => bool) tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed


code_pred [dseq] tranclp .
code_pred [random_dseq] tranclp .
thm tranclp.equation
thm tranclp.random_dseq_equation

inductive rtrancl' :: "'a => 'a => ('a => 'a => bool) => bool" 
where
  "rtrancl' x x r"
| "r x y ==> rtrancl' y z r ==> rtrancl' x z r"

code_pred [random_dseq] rtrancl' .

thm rtrancl'.random_dseq_equation

inductive rtrancl'' :: "('a * 'a * ('a \<Rightarrow> 'a \<Rightarrow> bool)) \<Rightarrow> bool"  
where
  "rtrancl'' (x, x, r)"
| "r x y \<Longrightarrow> rtrancl'' (y, z, r) \<Longrightarrow> rtrancl'' (x, z, r)"

code_pred rtrancl'' .

inductive rtrancl''' :: "('a * ('a * 'a) * ('a * 'a => bool)) => bool" 
where
  "rtrancl''' (x, (x, x), r)"
| "r (x, y) ==> rtrancl''' (y, (z, z), r) ==> rtrancl''' (x, (z, z), r)"

code_pred rtrancl''' .


inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
    "succ 0 1"
  | "succ m n \<Longrightarrow> succ (Suc m) (Suc n)"

code_pred (modes: i => i => bool, i => o => bool, o => i => bool, o => o => bool) succ .
code_pred [random_dseq] succ .
thm succ.equation
thm succ.random_dseq_equation

values 10 "{(m, n). succ n m}"
values "{m. succ 0 m}"
values "{m. succ m 0}"

text {* values command needs mode annotation of the parameter succ
to disambiguate which mode is to be chosen. *} 

values [mode: i => o => bool] 20 "{n. tranclp succ 10 n}"
values [mode: o => i => bool] 10 "{n. tranclp succ n 10}"
values 20 "{(n, m). tranclp succ n m}"

inductive example_graph :: "int => int => bool"
where
  "example_graph 0 1"
| "example_graph 1 2"
| "example_graph 1 3"
| "example_graph 4 7"
| "example_graph 4 5"
| "example_graph 5 6"
| "example_graph 7 6"
| "example_graph 7 8"
 
inductive not_reachable_in_example_graph :: "int => int => bool"
where "\<not> (tranclp example_graph x y) ==> not_reachable_in_example_graph x y"

code_pred (expected_modes: i => i => bool) not_reachable_in_example_graph .

thm not_reachable_in_example_graph.equation
thm tranclp.equation
value "not_reachable_in_example_graph 0 3"
value "not_reachable_in_example_graph 4 8"
value "not_reachable_in_example_graph 5 6"
text {* rtrancl compilation is strange! *}
(*
value "not_reachable_in_example_graph 0 4"
value "not_reachable_in_example_graph 1 6"
value "not_reachable_in_example_graph 8 4"*)

code_pred [dseq] not_reachable_in_example_graph .

values [dseq 6] "{x. tranclp example_graph 0 3}"

values [dseq 0] "{x. not_reachable_in_example_graph 0 3}"
values [dseq 0] "{x. not_reachable_in_example_graph 0 4}"
values [dseq 20] "{x. not_reachable_in_example_graph 0 4}"
values [dseq 6] "{x. not_reachable_in_example_graph 0 3}"
values [dseq 3] "{x. not_reachable_in_example_graph 4 2}"
values [dseq 6] "{x. not_reachable_in_example_graph 4 2}"


inductive not_reachable_in_example_graph' :: "int => int => bool"
where "\<not> (rtranclp example_graph x y) ==> not_reachable_in_example_graph' x y"

code_pred not_reachable_in_example_graph' .

value "not_reachable_in_example_graph' 0 3"
(* value "not_reachable_in_example_graph' 0 5" would not terminate *)


(*values [depth_limited 0] "{x. not_reachable_in_example_graph' 0 3}"*)
(*values [depth_limited 3] "{x. not_reachable_in_example_graph' 0 3}"*) (* fails with undefined *)
(*values [depth_limited 5] "{x. not_reachable_in_example_graph' 0 3}"*)
(*values [depth_limited 1] "{x. not_reachable_in_example_graph' 0 4}"*)
(*values [depth_limit = 4] "{x. not_reachable_in_example_graph' 0 4}"*) (* fails with undefined *)
(*values [depth_limit = 20] "{x. not_reachable_in_example_graph' 0 4}"*) (* fails with undefined *)

code_pred [dseq] not_reachable_in_example_graph' .

(*thm not_reachable_in_example_graph'.dseq_equation*)

(*values [dseq 0] "{x. not_reachable_in_example_graph' 0 3}"*)
(*values [depth_limited 3] "{x. not_reachable_in_example_graph' 0 3}"*) (* fails with undefined *)
(*values [depth_limited 5] "{x. not_reachable_in_example_graph' 0 3}"
values [depth_limited 1] "{x. not_reachable_in_example_graph' 0 4}"*)
(*values [depth_limit = 4] "{x. not_reachable_in_example_graph' 0 4}"*) (* fails with undefined *)
(*values [depth_limit = 20] "{x. not_reachable_in_example_graph' 0 4}"*) (* fails with undefined *)


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

values "{s. tupled_exec (While (%s. s!0 > 0) (Seq (Ass 0 (%s. s!0 - 1)) (Ass 1 (%s. s!1 + 1))), [3, 5], s)}"

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

values 3 
 "{as . steps (par (or (pre 0 nil) (pre 1 nil)) (pre 2 nil)) as (par nil nil)}"

values 5
 "{as . steps (par (or (pre 0 nil) (pre 1 nil)) (pre 2 nil)) as (par nil nil)}"

values 3 "{(a,q). step (par nil nil) a q}"


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
thm divmod_rel.equation
value [code] "Predicate.the (divmod_rel_i_i_o_o 1705 42)"

subsection {* Minimum *}

definition Min
where "Min s r x \<equiv> s x \<and> (\<forall>y. r x y \<longrightarrow> x = y)"

code_pred [inductify] Min .
thm Min.equation

subsection {* Lexicographic order *}

declare lexord_def[code_pred_def]
code_pred [inductify] lexord .
code_pred [random_dseq inductify] lexord .

thm lexord.equation
thm lexord.random_dseq_equation

inductive less_than_nat :: "nat * nat => bool"
where
  "less_than_nat (0, x)"
| "less_than_nat (x, y) ==> less_than_nat (Suc x, Suc y)"
 
code_pred less_than_nat .

code_pred [dseq] less_than_nat .
code_pred [random_dseq] less_than_nat .

inductive test_lexord :: "nat list * nat list => bool"
where
  "lexord less_than_nat (xs, ys) ==> test_lexord (xs, ys)"

code_pred test_lexord .
code_pred [dseq] test_lexord .
code_pred [random_dseq] test_lexord .
thm test_lexord.dseq_equation
thm test_lexord.random_dseq_equation

values "{x. test_lexord ([1, 2, 3], [1, 2, 5])}"
(*values [depth_limited 5] "{x. test_lexord ([1, 2, 3], [1, 2, 5])}"*)

declare list.size(3,4)[code_pred_def]
lemmas [code_pred_def] = lexn_conv lex_conv lenlex_conv
(*
code_pred [inductify] lexn .
thm lexn.equation
*)
(*
code_pred [random_dseq inductify] lexn .
thm lexn.random_dseq_equation

values [random_dseq 4, 4, 6] 100 "{(n, xs, ys::int list). lexn (%(x, y). x <= y) n (xs, ys)}"
*)
inductive has_length
where
  "has_length [] 0"
| "has_length xs i ==> has_length (x # xs) (Suc i)" 

lemma has_length:
  "has_length xs n = (length xs = n)"
proof (rule iffI)
  assume "has_length xs n"
  from this show "length xs = n"
    by (rule has_length.induct) auto
next
  assume "length xs = n"
  from this show "has_length xs n"
    by (induct xs arbitrary: n) (auto intro: has_length.intros)
qed

lemma lexn_intros [code_pred_intro]:
  "has_length xs i ==> has_length ys i ==> r (x, y) ==> lexn r (Suc i) (x # xs, y # ys)"
  "lexn r i (xs, ys) ==> lexn r (Suc i) (x # xs, x # ys)"
proof -
  assume "has_length xs i" "has_length ys i" "r (x, y)"
  from this has_length show "lexn r (Suc i) (x # xs, y # ys)"
    unfolding lexn_conv Collect_def mem_def
    by fastsimp
next
  assume "lexn r i (xs, ys)"
  thm lexn_conv
  from this show "lexn r (Suc i) (x#xs, x#ys)"
    unfolding Collect_def mem_def lexn_conv
    apply auto
    apply (rule_tac x="x # xys" in exI)
    by auto
qed

code_pred [random_dseq inductify] lexn
proof -
  fix n xs ys
  assume 1: "lexn r n (xs, ys)"
  assume 2: "\<And>i x xs' y ys'. r = r ==> n = Suc i ==> (xs, ys) = (x # xs', y # ys') ==> has_length xs' i ==> has_length ys' i ==> r (x, y) ==> thesis"
  assume 3: "\<And>i x xs' ys'. r = r ==> n = Suc i ==> (xs, ys) = (x # xs', x # ys') ==> lexn r i (xs', ys') ==> thesis"
  from 1 2 3 show thesis   
    unfolding lexn_conv Collect_def mem_def
    apply (auto simp add: has_length)
    apply (case_tac xys)
    apply auto
    apply fastsimp
    apply fastsimp done
qed


values [random_dseq 1, 2, 5] 10 "{(n, xs, ys::int list). lexn (%(x, y). x <= y) n (xs, ys)}"


code_pred [inductify] lenlex .
thm lenlex.equation

code_pred [random_dseq inductify] lenlex .
thm lenlex.random_dseq_equation

values [random_dseq 4, 2, 4] 100 "{(xs, ys::int list). lenlex (%(x, y). x <= y) (xs, ys)}"
thm lists.intros
(*
code_pred [inductify] lists .
*)
(*thm lists.equation*)

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
(*
code_pred [inductify] avl .
thm avl.equation*)

code_pred [random_dseq inductify] avl .
thm avl.random_dseq_equation

values [random_dseq 2, 1, 7] 5 "{t:: int tree. avl t}"

fun set_of
where
"set_of ET = {}"
| "set_of (MKT n l r h) = insert n (set_of l \<union> set_of r)"

fun is_ord :: "nat tree => bool"
where
"is_ord ET = True"
| "is_ord (MKT n l r h) =
 ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"

code_pred (expected_modes: i => o => bool, i => i => bool) [inductify] set_of .
thm set_of.equation

code_pred (expected_modes: i => bool) [inductify] is_ord .
thm is_ord_aux.equation
thm is_ord.equation


subsection {* Definitions about Relations *}
term "converse"
code_pred (modes:
  (i * i => bool) => i * i => bool,
  (i * o => bool) => o * i => bool,
  (i * o => bool) => i * i => bool,
  (o * i => bool) => i * o => bool,
  (o * i => bool) => i * i => bool,
  (o * o => bool) => o * o => bool,
  (o * o => bool) => i * o => bool,
  (o * o => bool) => o * i => bool,
  (o * o => bool) => i * i => bool) [inductify] converse .

thm converse.equation
code_pred [inductify] rel_comp .
thm rel_comp.equation
code_pred [inductify] Image .
thm Image.equation
declare singleton_iff[code_pred_inline]
declare Id_on_def[unfolded Bex_def UNION_def singleton_iff, code_pred_def]

code_pred (expected_modes:
  (o => bool) => o => bool,
  (o => bool) => i * o => bool,
  (o => bool) => o * i => bool,
  (o => bool) => i => bool,
  (i => bool) => i * o => bool,
  (i => bool) => o * i => bool,
  (i => bool) => i => bool) [inductify] Id_on .
thm Id_on.equation
thm Domain_def
code_pred (modes:
  (o * o => bool) => o => bool,
  (o * o => bool) => i => bool,
  (i * o => bool) => i => bool) [inductify] Domain .
thm Domain.equation
code_pred (modes:
  (o * o => bool) => o => bool,
  (o * o => bool) => i => bool,
  (o * i => bool) => i => bool) [inductify] Range .
thm Range.equation
code_pred [inductify] Field .
thm Field.equation
(*thm refl_on_def
code_pred [inductify] refl_on .
thm refl_on.equation*)
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

(*code_pred [inductify] length .
code_pred [random inductify] length .
thm size_listP.equation
thm size_listP.random_equation
*)
(*values [random] 1 "{xs. size_listP (xs::nat list) (5::nat)}"*)

code_pred (expected_modes: i => o => bool, o => i => bool, i => i => bool) [inductify] List.concat .
thm concatP.equation

values "{ys. concatP [[1, 2], [3, (4::int)]] ys}"
values "{ys. concatP [[1, 2], [3]] [1, 2, (3::nat)]}"

code_pred [dseq inductify] List.concat .
thm concatP.dseq_equation

values [dseq 3] 3
  "{xs. concatP xs ([0] :: nat list)}"

values [dseq 5] 3
  "{xs. concatP xs ([1] :: int list)}"

values [dseq 5] 3
  "{xs. concatP xs ([1] :: nat list)}"

values [dseq 5] 3
  "{xs. concatP xs [(1::int), 2]}"

code_pred (expected_modes: i => o => bool, i => i => bool) [inductify] hd .
thm hdP.equation
values "{x. hdP [1, 2, (3::int)] x}"
values "{(xs, x). hdP [1, 2, (3::int)] 1}"
 
code_pred (expected_modes: i => o => bool, i => i => bool) [inductify] tl .
thm tlP.equation
values "{x. tlP [1, 2, (3::nat)] x}"
values "{x. tlP [1, 2, (3::int)] [3]}"

code_pred [inductify] last .
thm lastP.equation

code_pred [inductify] butlast .
thm butlastP.equation

code_pred [inductify] take .
thm takeP.equation

code_pred [inductify] drop .
thm dropP.equation
code_pred [inductify] zip .
thm zipP.equation

code_pred [inductify] upt .
code_pred [inductify] remdups .
thm remdupsP.equation
code_pred [dseq inductify] remdups .
values [dseq 4] 5 "{xs. remdupsP xs [1, (2::int)]}"

code_pred [inductify] remove1 .
thm remove1P.equation
values "{xs. remove1P 1 xs [2, (3::int)]}"

code_pred [inductify] removeAll .
thm removeAllP.equation
code_pred [dseq inductify] removeAll .

values [dseq 4] 10 "{xs. removeAllP 1 xs [(2::nat)]}"

code_pred [inductify] distinct .
thm distinct.equation
code_pred [inductify] replicate .
thm replicateP.equation
values 5 "{(n, xs). replicateP n (0::int) xs}"

code_pred [inductify] splice .
thm splice.simps
thm spliceP.equation

values "{xs. spliceP xs [1, 2, 3] [1, 1, 1, 2, 1, (3::nat)]}"

code_pred [inductify] List.rev .
code_pred [inductify] map .
code_pred [inductify] foldr .
code_pred [inductify] foldl .
code_pred [inductify] filter .
code_pred [random_dseq inductify] filter .

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
code_pred [random_dseq inductify] S\<^isub>1p .
thm S\<^isub>1p.equation
thm S\<^isub>1p.random_dseq_equation

values [random_dseq 5, 5, 5] 5 "{x. S\<^isub>1p x}"

inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"

code_pred [random_dseq inductify] S\<^isub>2p .
thm S\<^isub>2p.random_dseq_equation
thm A\<^isub>2p.random_dseq_equation
thm B\<^isub>2p.random_dseq_equation

values [random_dseq 5, 5, 5] 10 "{x. S\<^isub>2p x}"

inductive_set S\<^isub>3 and A\<^isub>3 and B\<^isub>3 where
  "[] \<in> S\<^isub>3"
| "w \<in> A\<^isub>3 \<Longrightarrow> b # w \<in> S\<^isub>3"
| "w \<in> B\<^isub>3 \<Longrightarrow> a # w \<in> S\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> a # w \<in> A\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> b # w \<in> B\<^isub>3"
| "\<lbrakk>v \<in> B\<^isub>3; w \<in> B\<^isub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>3"

code_pred [inductify] S\<^isub>3p .
thm S\<^isub>3p.equation

values 10 "{x. S\<^isub>3p x}"

inductive_set S\<^isub>4 and A\<^isub>4 and B\<^isub>4 where
  "[] \<in> S\<^isub>4"
| "w \<in> A\<^isub>4 \<Longrightarrow> b # w \<in> S\<^isub>4"
| "w \<in> B\<^isub>4 \<Longrightarrow> a # w \<in> S\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> a # w \<in> A\<^isub>4"
| "\<lbrakk>v \<in> A\<^isub>4; w \<in> A\<^isub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> b # w \<in> B\<^isub>4"
| "\<lbrakk>v \<in> B\<^isub>4; w \<in> B\<^isub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>4"

code_pred (expected_modes: o => bool, i => bool) S\<^isub>4p .

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

code_pred (expected_modes: i => i => o => bool, i => i => i => bool) typing .
thm typing.equation

code_pred (modes: i => i => bool,  i => o => bool as reduce') beta .
thm beta.equation

values "{x. App (Abs (Atom 0) (Var 0)) (Var 1) \<rightarrow>\<^sub>\<beta> x}"

definition "reduce t = Predicate.the (reduce' t)"

value "reduce (App (Abs (Atom 0) (Var 0)) (Var 1))"

code_pred [dseq] typing .
code_pred [random_dseq] typing .

values [random_dseq 1,1,5] 10 "{(\<Gamma>, t, T). \<Gamma> \<turnstile> t : T}"

subsection {* A minimal example of yet another semantics *}

text {* thanks to Elke Salecker *}

types
  vname = nat
  vvalue = int
  var_assign = "vname \<Rightarrow> vvalue"  --"variable assignment"

datatype ir_expr = 
  IrConst vvalue
| ObjAddr vname
| Add ir_expr ir_expr

datatype val =
  IntVal  vvalue

record  configuration =
  Env :: var_assign

inductive eval_var ::
  "ir_expr \<Rightarrow> configuration \<Rightarrow> val \<Rightarrow> bool"
where
  irconst: "eval_var (IrConst i) conf (IntVal i)"
| objaddr: "\<lbrakk> Env conf n = i \<rbrakk> \<Longrightarrow> eval_var (ObjAddr n) conf (IntVal i)"
| plus: "\<lbrakk> eval_var l conf (IntVal vl); eval_var r conf (IntVal vr) \<rbrakk> \<Longrightarrow> eval_var (Add l r) conf (IntVal (vl+vr))"


code_pred eval_var .
thm eval_var.equation

values "{val. eval_var (Add (IrConst 1) (IrConst 2)) (| Env = (\<lambda>x. 0)|) val}"

end