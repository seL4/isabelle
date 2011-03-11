(*  Title:      HOL/ex/Quickcheck_Narrowing_Examples.thy
    Author:     Lukas Bulwahn
    Copyright   2011 TU Muenchen
*)

header {* Examples for narrowing-based testing  *}

theory Quickcheck_Narrowing_Examples
imports "~~/src/HOL/Library/LSC"
begin

subsection {* Simple list examples *}

lemma "rev xs = xs"
quickcheck[tester = lazy_exhaustive, finite_types = false, default_type = nat, expect = counterexample]
oops

text {* Example fails due to some strange thing... *}
(*
lemma "rev xs = xs"
quickcheck[tester = lazy_exhaustive, finite_types = true]
oops
*)

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
                 
subsection {* Necessary instantiation for quickcheck generator *}

instantiation tree :: (serial) serial
begin

function series_tree
where
  "series_tree d = sum (cons ET) (apply (apply (apply (apply (cons MKT) series) series_tree) series_tree) series) d"
by pat_completeness auto

termination proof (relation "measure nat_of")
qed (auto simp add: of_int_inverse nat_of_def)

instance ..

end

subsubsection {* Invalid Lemma due to typo in lbal *}

lemma is_ord_l_bal:
 "\<lbrakk> is_ord(MKT (x :: nat) l r h); height l = height r + 2 \<rbrakk> \<Longrightarrow> is_ord(l_bal(x,l,r))"
quickcheck[tester = lazy_exhaustive, finite_types = false, default_type = nat, size = 1, timeout = 100, expect = counterexample]
oops


end
