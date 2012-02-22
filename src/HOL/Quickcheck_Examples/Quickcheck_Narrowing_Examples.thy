(*  Title:      HOL/ex/Quickcheck_Narrowing_Examples.thy
    Author:     Lukas Bulwahn
    Copyright   2011 TU Muenchen
*)

header {* Examples for narrowing-based testing  *}

theory Quickcheck_Narrowing_Examples
imports Main
begin

declare [[quickcheck_timeout = 3600]]

subsection {* Minimalistic examples *}

lemma
  "x = y"
quickcheck[tester = narrowing, finite_types = false, default_type = int, expect = counterexample]
oops

lemma
  "x = y"
quickcheck[tester = narrowing, finite_types = false, default_type = nat, expect = counterexample]
oops

subsection {* Simple examples with existentials *}

lemma
  "\<exists> y :: nat. \<forall> x. x = y"
quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops
(*
lemma
  "\<exists> y :: int. \<forall> x. x = y"
quickcheck[tester = narrowing, size = 2]
oops
*)
lemma
  "x > 1 --> (\<exists>y :: nat. x < y & y <= 1)"
quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops

lemma
  "x > 2 --> (\<exists>y :: nat. x < y & y <= 2)"
quickcheck[tester = narrowing, finite_types = false, size = 10]
oops

lemma
  "\<forall> x. \<exists> y :: nat. x > 3 --> (y < x & y > 3)"
quickcheck[tester = narrowing, finite_types = false, size = 7]
oops

text {* A false conjecture derived from an partial copy-n-paste of @{thm not_distinct_decomp} *}
lemma
  "~ distinct ws ==> EX xs ys zs y. ws = xs @ [y] @ ys @ [y]"
quickcheck[tester = narrowing, finite_types = false, default_type = nat, expect = counterexample]
oops

text {* A false conjecture derived from theorems @{thm split_list_first} and @{thm split_list_last} *}  
lemma
  "x : set xs ==> EX ys zs. xs = ys @ x # zs & x ~: set zs & x ~: set ys"
quickcheck[tester = narrowing, finite_types = false, default_type = nat, expect = counterexample]
oops

text {* A false conjecture derived from @{thm map_eq_Cons_conv} with a typo *}
lemma
  "(map f xs = y # ys) = (EX z zs. xs = z' # zs & f z = y & map f zs = ys)"
quickcheck[tester = narrowing, finite_types = false, default_type = nat, expect = counterexample]
oops

lemma "a # xs = ys @ [a] ==> EX zs. xs = zs @ [a] & ys = a#zs"
quickcheck[narrowing, expect = counterexample]
quickcheck[exhaustive, random, expect = no_counterexample]
oops

subsection {* Simple list examples *}

lemma "rev xs = xs"
quickcheck[tester = narrowing, finite_types = false, default_type = nat, expect = counterexample]
oops

(* FIXME: integer has strange representation! *)
lemma "rev xs = xs"
quickcheck[tester = narrowing, finite_types = false, default_type = int, expect = counterexample]
oops
(*
lemma "rev xs = xs"
  quickcheck[tester = narrowing, finite_types = true, expect = counterexample]
oops
*)
subsection {* Simple examples with functions *}

lemma "map f xs = map g xs"
  quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops

lemma "map f xs = map f ys ==> xs = ys"
  quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops

lemma
  "list_all2 P (rev xs) (rev ys) = list_all2 P xs (rev ys)"
  quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops

lemma "map f xs = F f xs"
  quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops

lemma "map f xs = F f xs"
  quickcheck[tester = narrowing, finite_types = false, expect = counterexample]
oops

(* requires some work...*)
(*
lemma "R O S = S O R"
  quickcheck[tester = narrowing, size = 2]
oops
*)

subsection {* Simple examples with inductive predicates *}

inductive even where
  "even 0" |
  "even n ==> even (Suc (Suc n))"

code_pred even .

lemma "even (n - 2) ==> even n"
quickcheck[narrowing, expect = counterexample]
oops


subsection {* AVL Trees *}

datatype 'a tree = ET |  MKT 'a "'a tree" "'a tree" nat

primrec set_of :: "'a tree \<Rightarrow> 'a set"
where
"set_of ET = {}" |
"set_of (MKT n l r h) = insert n (set_of l \<union> set_of r)"

primrec height :: "'a tree \<Rightarrow> nat"
where
"height ET = 0" |
"height (MKT x l r h) = max (height l) (height r) + 1"

primrec avl :: "'a tree \<Rightarrow> bool"
where
"avl ET = True" |
"avl (MKT x l r h) =
 ((height l = height r \<or> height l = 1+height r \<or> height r = 1+height l) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

primrec is_ord :: "('a::order) tree \<Rightarrow> bool"
where
"is_ord ET = True" |
"is_ord (MKT n l r h) =
 ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"

primrec is_in :: "('a::order) \<Rightarrow> 'a tree \<Rightarrow> bool"
where
 "is_in k ET = False" |
 "is_in k (MKT n l r h) = (if k = n then True else
                           if k < n then (is_in k l)
                           else (is_in k r))"

primrec ht :: "'a tree \<Rightarrow> nat"
where
"ht ET = 0" |
"ht (MKT x l r h) = h"

definition
 mkt :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"mkt x l r = MKT x l r (max (ht l) (ht r) + 1)"

(* replaced MKT lrn lrl lrr by MKT lrr lrl *)
fun l_bal where
"l_bal(n, MKT ln ll lr h, r) =
 (if ht ll < ht lr
  then case lr of ET \<Rightarrow> ET (* impossible *)
                | MKT lrn lrr lrl lrh \<Rightarrow>
                  mkt lrn (mkt ln ll lrl) (mkt n lrr r)
  else mkt ln ll (mkt n lr r))"

fun r_bal where
"r_bal(n, l, MKT rn rl rr h) =
 (if ht rl > ht rr
  then case rl of ET \<Rightarrow> ET (* impossible *)
                | MKT rln rll rlr h \<Rightarrow> mkt rln (mkt n l rll) (mkt rn rlr rr)
  else mkt rn (mkt n l rl) rr)"

primrec insrt :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
"insrt x ET = MKT x ET ET 1" |
"insrt x (MKT n l r h) = 
   (if x=n
    then MKT n l r h
    else if x<n
         then let l' = insrt x l; hl' = ht l'; hr = ht r
              in if hl' = 2+hr then l_bal(n,l',r)
                 else MKT n l' r (1 + max hl' hr)
         else let r' = insrt x r; hl = ht l; hr' = ht r'
              in if hr' = 2+hl then r_bal(n,l,r')
                 else MKT n l r' (1 + max hl hr'))"


subsubsection {* Necessary setup for code generation *}

primrec set_of'
where 
  "set_of' ET = []"
| "set_of' (MKT n l r h) = n # (set_of' l @ set_of' r)"

lemma set_of':
  "set (set_of' t) = set_of t"
by (induct t) auto

lemma is_ord_mkt:
  "is_ord (MKT n l r h) = ((ALL n': set (set_of' l). n' < n) & (ALL n': set (set_of' r). n < n') & is_ord l & is_ord r)"
by (simp add: set_of')

declare is_ord.simps(1)[code] is_ord_mkt[code]

subsubsection {* Invalid Lemma due to typo in lbal *}

lemma is_ord_l_bal:
 "\<lbrakk> is_ord(MKT (x :: nat) l r h); height l = height r + 2 \<rbrakk> \<Longrightarrow> is_ord(l_bal(x,l,r))"
quickcheck[tester = narrowing, finite_types = false, default_type = nat, size = 6, expect = counterexample]
oops

subsection {* Examples with hd and last *}

lemma
  "hd (xs @ ys) = hd ys"
quickcheck[narrowing, expect = counterexample]
oops

lemma
  "last(xs @ ys) = last xs"
quickcheck[narrowing, expect = counterexample]
oops

subsection {* Examples with underspecified/partial functions *}

lemma
  "xs = [] ==> hd xs \<noteq> x"
quickcheck[narrowing, expect = no_counterexample]
oops

lemma
  "xs = [] ==> hd xs = x"
quickcheck[narrowing, expect = no_counterexample]
oops

lemma "xs = [] ==> hd xs = x ==> x = y"
quickcheck[narrowing, expect = no_counterexample]
oops

lemma
  "hd (xs @ ys) = (if xs = [] then hd ys else hd xs)"
quickcheck[narrowing, expect = no_counterexample]
oops

lemma
  "hd (map f xs) = f (hd xs)"
quickcheck[narrowing, expect = no_counterexample]
oops

end
