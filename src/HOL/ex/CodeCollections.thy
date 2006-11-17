(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Collection classes as examples for code generation *}

theory CodeCollections
imports Main
begin

section {* Collection classes as examples for code generation *}

class ordered = eq +
  constrains eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^loc><<=" 65)
  fixes lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^loc><<" 65)
  assumes order_refl: "x \<^loc><<= x"
  assumes order_trans: "x \<^loc><<= y ==> y \<^loc><<= z ==> x \<^loc><<= z"
  assumes order_antisym: "x \<^loc><<= y ==> y \<^loc><<= x ==> x = y"

declare order_refl [simp, intro]

defs
  lt_def: "x << y == (x <<= y \<and> x \<noteq> y)"

lemma lt_intro [intro]:
  assumes "x <<= y" and "x \<noteq> y"
  shows "x << y"
unfolding lt_def ..

lemma lt_elim [elim]:
  assumes "(x::'a::ordered) << y"
  and Q: "!!x y::'a::ordered. x <<= y \<Longrightarrow> x \<noteq> y \<Longrightarrow> P"
  shows P
proof -
  from prems have R1: "x <<= y" and R2: "x \<noteq> y" by (simp_all add: lt_def)
  show P by (rule Q [OF R1 R2])
qed

lemma lt_trans:
  assumes "x << y" and "y << z"
  shows "x << z"
proof
  from prems lt_def have prems': "x <<= y" "y <<= z" by auto
  show "x <<= z" by (rule order_trans, auto intro: prems')
next
  show "x \<noteq> z"
  proof
    from prems lt_def have prems': "x <<= y" "y <<= z" "x \<noteq> y" by auto
    assume "x = z"
    with prems' have "x <<= y" and "y <<= x" by auto
    with order_antisym have "x = y" .
    with prems' show False by auto
  qed
qed

definition (in ordered)
  min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min x y = (if x \<^loc><<= y then x else y)"

definition (in ordered)
  max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max x y = (if x \<^loc><<= y then y else x)"

definition
  min :: "'a::ordered \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min x y = (if x <<= y then x else y)"

definition
  max :: "'a::ordered \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max x y = (if x <<= y then y else x)"

fun abs_sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "abs_sorted cmp [] = True"
| "abs_sorted cmp [x] = True"
| "abs_sorted cmp (x#y#xs) = (cmp x y \<and> abs_sorted cmp (y#xs))"

thm abs_sorted.simps

abbreviation (in ordered)
  "sorted \<equiv> abs_sorted le"

abbreviation
  "sorted \<equiv> abs_sorted le"

lemma (in ordered) sorted_weakening:
  assumes "sorted (x # xs)"
  shows "sorted xs"
using prems proof (induct xs)
  case Nil show ?case by simp 
next
  case (Cons x' xs)
  from this(5) have "sorted (x # x' # xs)" .
  then show "sorted (x' # xs)"
    by auto
qed

instance bool :: ordered
  "p <<= q == (p --> q)"
  by default (unfold ordered_bool_def, blast+)

instance nat :: ordered
  "m <<= n == m <= n"
  by default (simp_all add: ordered_nat_def)

instance int :: ordered
  "k <<= l == k <= l"
  by default (simp_all add: ordered_int_def)

instance unit :: ordered
  "u <<= v == True"
  by default (simp_all add:  ordered_unit_def)


fun le_option' :: "'a::ordered option \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "le_option' None y = True"
| "le_option' (Some x) None = False"
| "le_option' (Some x) (Some y) = x <<= y"

instance option :: (ordered) ordered
  "x <<= y == le_option' x y"
proof (default, unfold ordered_option_def)
  fix x
  show "le_option' x x" by (cases x) simp_all
next
  fix x y z
  assume "le_option' x y" "le_option' y z"
  then show "le_option' x z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
    (erule order_trans, assumption)
next
  fix x y
  assume "le_option' x y" "le_option' y x"
  then show "x = y"
    by (cases x, simp_all, cases y, simp_all, cases y, simp_all)
    (erule order_antisym, assumption)
qed

lemma [simp, code]:
  "None <<= y = True"
  "Some x <<= None = False"
  "Some v <<= Some w = v <<= w"
  unfolding ordered_option_def le_option'.simps by rule+

fun le_pair' :: "'a::ordered \<times> 'b::ordered \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "le_pair' (x1, y1) (x2, y2) = (x1 << x2 \<or> x1 = x2 \<and> y1 <<= y2)"

instance * :: (ordered, ordered) ordered
  "x <<= y == le_pair' x y"
apply (default, unfold "ordered_*_def", unfold split_paired_all)
apply simp_all
apply (auto intro: lt_trans order_trans)[1]
unfolding lt_def apply (auto intro: order_antisym)[1]
done

lemma [simp, code]:
  "(x1, y1) <<= (x2, y2) = (x1 << x2 \<or> x1 = x2 \<and> y1 <<= y2)"
  unfolding "ordered_*_def" le_pair'.simps ..

(*   

fun le_list' :: "'a::ordered list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "le_list' [] ys = True"
| "le_list' (x#xs) [] = False"
| "le_list' (x#xs) (y#ys) = (x << y \<or> x = y \<and> le_list' xs ys)"

instance (ordered) list :: ordered
  "xs <<= ys == le_list' xs ys"
proof (default, unfold "ordered_list_def")
  fix xs
  show "le_list' xs xs" by (induct xs) simp_all
next
  fix xs ys zs
  assume "le_list' xs ys" and "le_list' ys zs"
  then show "le_list' xs zs"
  apply (induct xs zs rule: le_list'.induct)
  apply simp_all
  apply (cases ys) apply simp_all
  
  apply (induct ys) apply simp_all
  apply (induct ys)
  apply simp_all
  apply (induct zs)
  apply simp_all
next
  fix xs ys
  assume "le_list' xs ys" and "le_list' ys xs"
  show "xs = ys" sorry
qed

lemma [simp, code]:
  "[] <<= ys = True"
  "(x#xs) <<= [] = False"
  "(x#xs) <<= (y#ys) = (x << y \<or> x = y \<and> xs <<= ys)"
  unfolding "ordered_list_def" le_list'.simps by rule+*)

class infimum = ordered +
  fixes inf
  assumes inf: "inf \<^loc><<= x"

lemma (in infimum)
  assumes prem: "a \<^loc><<= inf"
  shows no_smaller: "a = inf"
using prem inf by (rule order_antisym)


ML {* set quick_and_dirty *}
function abs_max_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a"
where
  "abs_max_of cmp inff [] = inff"
| "abs_max_of cmp inff [x] = x"
| "abs_max_of cmp inff (x#xs) =
     ordered.max cmp x (abs_max_of cmp inff xs)"
apply pat_completeness sorry

abbreviation (in infimum)
  "max_of xs \<equiv> abs_max_of le inf"

abbreviation
  "max_of xs \<equiv> abs_max_of le inf"

instance bool :: infimum
  "inf == False"
  by default (simp add: infimum_bool_def)

instance nat :: infimum
  "inf == 0"
  by default (simp add: infimum_nat_def)

instance unit :: infimum
  "inf == ()"
  by default (simp add: infimum_unit_def)

instance option :: (ordered) infimum
  "inf == None"
  by default (simp add: infimum_option_def)

instance * :: (infimum, infimum) infimum
  "inf == (inf, inf)"
  by default (unfold "infimum_*_def", unfold split_paired_all, auto intro: inf)

class enum = ordered +
  fixes enum :: "'a list"
  assumes member_enum: "x \<in> set enum"
  and ordered_enum: "abs_sorted le enum"

(*
FIXME:
- abbreviations must be propagated before locale introduction
- then also now shadowing may occur
*)
(*abbreviation (in enum)
  "local.sorted \<equiv> abs_sorted le"*)

instance bool :: enum
  (* FIXME: better name handling of definitions *)
  "_1": "enum == [False, True]"
  by default (simp_all add: enum_bool_def)

instance unit :: enum
  "_2": "enum == [()]"
  by default (simp_all add: enum_unit_def)

(*consts
  product :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"

primrec
  "product [] ys = []"
  "product (x#xs) ys = map (Pair x) ys @ product xs ys"

lemma product_all:
  assumes "x \<in> set xs" "y \<in> set ys"
  shows "(x, y) \<in> set (product xs ys)"
using prems proof (induct xs)
  case Nil
  then have False by auto
  then show ?case ..
next
  case (Cons z xs)
  then show ?case
  proof (cases "x = z")
    case True
    with Cons have "(x, y) \<in> set (product (x # xs) ys)" by simp
    with True show ?thesis by simp
  next
    case False
    with Cons have "x \<in> set xs" by auto
    with Cons have "(x, y) \<in> set (product xs ys)" by auto
    then show "(x, y) \<in> set (product (z#xs) ys)" by auto
  qed
qed

lemma product_sorted:
  assumes "sorted xs" "sorted ys"
  shows "sorted (product xs ys)"
using prems proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons ordered.sorted_weakening have "sorted xs" by auto
  with Cons have "sorted (product xs ys)" by auto
  then show ?case apply simp
  proof -
    assume 
apply simp
  
  proof (cases "x = z")
    case True
    with Cons have "(x, y) \<in> set (product (x # xs) ys)" by simp
    with True show ?thesis by simp
  next
    case False
    with Cons have "x \<in> set xs" by auto
    with Cons have "(x, y) \<in> set (product xs ys)" by auto
    then show "(x, y) \<in> set (product (z#xs) ys)" by auto
  qed
qed

instance (enum, enum) * :: enum
  "_3": "enum == product enum enum"
apply default
apply (simp_all add: "enum_*_def")
apply (unfold split_paired_all)
apply (rule product_all)
apply (rule member_enum)+
sorry*)

instance option :: (enum) enum
  "_4": "enum == None # map Some enum"
proof (default, unfold enum_option_def)
  fix x :: "'a::enum option"
  show "x \<in> set (None # map Some enum)"
  proof (cases x)
    case None then show ?thesis by auto
  next
    case (Some x) then show ?thesis by (auto intro: member_enum)
  qed
next
  show "sorted (None # map Some (enum :: ('a::enum) list))"
  sorry
  (*proof (cases "enum :: 'a list")
    case Nil then show ?thesis by simp
  next
   case (Cons x xs)
   then have "sorted (None # map Some (x # xs))" sorry
   then show ?thesis apply simp
  apply simp_all
  apply auto*)
qed

ML {* reset quick_and_dirty *}

consts
  get_first :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"

primrec
  "get_first p [] = None"
  "get_first p (x#xs) = (if p x then Some x else get_first p xs)"

consts
  get_index :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat option"

primrec
  "get_index p n [] = None"
  "get_index p n (x#xs) = (if p x then Some n else get_index p (Suc n) xs)"

definition
  between :: "'a::enum \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "between x y = get_first (\<lambda>z. x << z & z << y) enum"

definition
  index :: "'a::enum \<Rightarrow> nat" where
  "index x = the (get_index (\<lambda>y. y = x) 0 enum)"

definition
  add :: "'a::enum \<Rightarrow> 'a \<Rightarrow> 'a" where
  "add x y =
    (let
      enm = enum
    in enm ! ((index x + index y) mod length enm))"

consts
  sum :: "'a::{enum, infimum} list \<Rightarrow> 'a"

primrec
  "sum [] = inf"
  "sum (x#xs) = add x (sum xs)"

definition "test1 = sum [None, Some True, None, Some False]"
definition "test2 = (inf :: nat \<times> unit)"

code_gen "op <<="
code_gen "op <<"
code_gen inf
code_gen between
code_gen index
code_gen test1
code_gen test2

code_gen (SML *)
code_gen (Haskell -)

end