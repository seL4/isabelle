 (*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Collection classes as examples for code generation *}

theory CodeCollections
imports Main Product_ord List_lexord
begin

section {* Collection classes as examples for code generation *}

fun
  abs_sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "abs_sorted cmp [] \<longleftrightarrow> True"
  "abs_sorted cmp [x] \<longleftrightarrow> True"
  "abs_sorted cmp (x#y#xs) \<longleftrightarrow> cmp x y \<and> abs_sorted cmp (y#xs)"

abbreviation (in ord)
  "sorted \<equiv> abs_sorted less_eq"

abbreviation
  "sorted \<equiv> abs_sorted less_eq"

lemma (in partial_order) sorted_weakening:
  assumes "sorted (x # xs)"
  shows "sorted xs"
using prems proof (induct xs)
  case Nil show ?case by simp 
next
  case (Cons x' xs)
  from this have "sorted (x # x' # xs)" by auto
  then show "sorted (x' # xs)"
    by auto
qed

instance unit :: order
  "u \<le> v \<equiv> True"
  "u < v \<equiv> False"
  by default (simp_all add: less_eq_unit_def less_unit_def)

fun le_option' :: "'a\<Colon>order option \<Rightarrow> 'a option \<Rightarrow> bool"
  where "le_option' None y \<longleftrightarrow> True"
  | "le_option' (Some x) None \<longleftrightarrow> False"
  | "le_option' (Some x) (Some y) \<longleftrightarrow> x \<le> y"

instance option :: (order) order
  "x \<le> y \<equiv> le_option' x y"
  "x < y \<equiv> x \<le> y \<and> x \<noteq> y"
proof (default, unfold less_eq_option_def less_option_def)
  fix x
  show "le_option' x x" by (cases x) simp_all
next
  fix x y z
  assume "le_option' x y" "le_option' y z"
  then show "le_option' x z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
next
  fix x y
  assume "le_option' x y" "le_option' y x"
  then show "x = y"
    by (cases x, simp_all, cases y, simp_all, cases y, simp_all)
next
  fix x y
  show "le_option' x y \<and> x \<noteq> y \<longleftrightarrow> le_option' x y \<and> x \<noteq> y" ..
qed

lemma [simp, code]:
  "None \<le> y \<longleftrightarrow> True"
  "Some x \<le> None \<longleftrightarrow> False"
  "Some v \<le> Some w \<longleftrightarrow> v \<le> w"
  unfolding less_eq_option_def less_option_def le_option'.simps by rule+

lemma forall_all [simp]:
  "list_all P xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x)"
  by (induct xs) auto

lemma exists_ex [simp]:
  "list_ex P xs \<longleftrightarrow> (\<exists>x\<in>set xs. P x)"
  by (induct xs) auto

class fin =
  fixes fin :: "'a list"
  assumes member_fin: "x \<in> set fin"
begin

lemma set_enum_UNIV:
  "set fin = UNIV"
  using member_fin by auto

lemma all_forall [code func, code inline]:
  "(\<forall>x. P x) \<longleftrightarrow> list_all P fin"
  using set_enum_UNIV by simp_all

lemma ex_exists [code func, code inline]:
  "(\<exists>x. P x) \<longleftrightarrow> list_ex P fin"
  using set_enum_UNIV by simp_all

end
  
instance bool :: fin
  "fin == [False, True]"
  by default (simp_all add: fin_bool_def)

instance unit :: fin
  "fin == [()]"
  by default (simp_all add: fin_unit_def)

fun
  product :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"
  where
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

instance * :: (fin, fin) fin
  "fin == product fin fin"
apply default
apply (simp_all add: "fin_*_def")
apply (unfold split_paired_all)
apply (rule product_all)
apply (rule member_fin)+
done

instance option :: (fin) fin
  "fin == None # map Some fin"
proof (default, unfold fin_option_def)
  fix x :: "'a::fin option"
  show "x \<in> set (None # map Some fin)"
  proof (cases x)
    case None then show ?thesis by auto
  next
    case (Some x) then show ?thesis by (auto intro: member_fin)
  qed
qed

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

(*definition
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
  "sum (x#xs) = add x (sum xs)"*)

(*definition "test1 = sum [None, Some True, None, Some False]"*)
(*definition "test2 = (inf :: nat \<times> unit)"*)
definition "test3 \<longleftrightarrow> (\<exists>x \<Colon> bool option. case x of Some P \<Rightarrow> P | None \<Rightarrow> False)"

code_gen test3

code_gen (SML #)
code_gen (Haskell -)

end