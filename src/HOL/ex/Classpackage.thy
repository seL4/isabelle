(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Test and examples for Isar class package *}

theory Classpackage
imports List
begin

class semigroup = type +
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)"

instance nat :: semigroup
  "m \<otimes> n \<equiv> (m\<Colon>nat) + n"
proof
  fix m n q :: nat 
  from mult_nat_def show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)" by simp
qed

instance int :: semigroup
  "k \<otimes> l \<equiv> (k\<Colon>int) + l"
proof
  fix k l j :: int
  from mult_int_def show "k \<otimes> l \<otimes> j = k \<otimes> (l \<otimes> j)" by simp
qed

instance * :: (semigroup, semigroup) semigroup
  mult_prod_def: "x \<otimes> y \<equiv> let (x1, x2) = x; (y1, y2) = y in
              (x1 \<otimes> y1, x2 \<otimes> y2)"
by default (simp_all add: split_paired_all mult_prod_def assoc)

instance list :: (type) semigroup
  "xs \<otimes> ys \<equiv> xs @ ys"
proof
  fix xs ys zs :: "'a list"
  show "xs \<otimes> ys \<otimes> zs = xs \<otimes> (ys \<otimes> zs)"
  proof -
    from mult_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
    thus ?thesis by simp
  qed
qed

class monoidl = semigroup +
  fixes one :: 'a ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"

instance nat :: monoidl and int :: monoidl
  "\<one> \<equiv> (0\<Colon>nat)"
  "\<one> \<equiv> (0\<Colon>int)"
proof
  fix n :: nat
  from mult_nat_def one_nat_def show "\<one> \<otimes> n = n" by simp
next
  fix k :: int
  from mult_int_def one_int_def show "\<one> \<otimes> k = k" by simp
qed

instance * :: (monoidl, monoidl) monoidl
  one_prod_def: "\<one> \<equiv> (\<one>, \<one>)"
by default (simp_all add: split_paired_all mult_prod_def one_prod_def neutl)

instance list :: (type) monoidl
  "\<one> \<equiv> []"
proof
  fix xs :: "'a list"
  show "\<one> \<otimes> xs = xs"
  proof -
    from mult_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
    moreover from one_list_def have "\<one> \<equiv> []\<Colon>'a list" by simp
    ultimately show ?thesis by simp
  qed
qed  

class monoid = monoidl +
  assumes neutr: "x \<otimes> \<one> = x"
begin

definition
  units :: "'a set" where
  "units = {y. \<exists>x. x \<otimes> y = \<one> \<and> y \<otimes> x = \<one>}"

lemma inv_obtain:
  assumes "x \<in> units"
  obtains y where "y \<otimes> x = \<one>" and "x \<otimes> y = \<one>"
proof -
  from assms units_def obtain y
    where "y \<otimes> x = \<one>" and "x \<otimes> y = \<one>" by auto
  thus ?thesis ..
qed

lemma inv_unique:
  assumes "y \<otimes> x = \<one>" "x \<otimes> y' = \<one>"
  shows "y = y'"
proof -
  from assms neutr have "y = y \<otimes> (x \<otimes> y')" by simp
  also with assoc have "... = (y \<otimes> x) \<otimes> y'" by simp
  also with assms neutl have "... = y'" by simp
  finally show ?thesis .
qed

lemma units_inv_comm:
  assumes inv: "x \<otimes> y = \<one>"
    and G: "x \<in> units"
  shows "y \<otimes> x = \<one>"
proof -
  from G inv_obtain obtain z
    where z_choice: "z \<otimes> x = \<one>" by blast
  from inv neutl neutr have "x \<otimes> y \<otimes> x = x \<otimes> \<one>" by simp
  with assoc have "z \<otimes> x \<otimes> y \<otimes> x = z \<otimes> x \<otimes> \<one>" by simp
  with neutl z_choice show ?thesis by simp
qed

fun
  npow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "npow 0 x = \<one>"
  | "npow (Suc n) x = x \<otimes> npow n x"

abbreviation
  npow_syn :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "\<up>" 75) where
  "x \<up> n \<equiv> npow n x"

lemma nat_pow_one:
  "\<one> \<up> n = \<one>"
using neutl by (induct n) simp_all

lemma nat_pow_mult: "x \<up> n \<otimes> x \<up> m = x \<up> (n + m)"
proof (induct n)
  case 0 with neutl show ?case by simp
next
  case (Suc n) with Suc.hyps assoc show ?case by simp
qed

lemma nat_pow_pow: "(x \<up> m) \<up> n = x \<up> (n * m)"
using nat_pow_mult by (induct n) simp_all

end

instance * :: (monoid, monoid) monoid
by default (simp_all add: split_paired_all mult_prod_def one_prod_def neutr)

instance list :: (type) monoid
proof
  fix xs :: "'a list"
  show "xs \<otimes> \<one> = xs"
  proof -
    from mult_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
    moreover from one_list_def have "\<one> \<equiv> []\<Colon>'a list" by simp
    ultimately show ?thesis by simp
  qed
qed  

class monoid_comm = monoid +
  assumes comm: "x \<otimes> y = y \<otimes> x"

instance nat :: monoid_comm and int :: monoid_comm
proof
  fix n :: nat
  from mult_nat_def one_nat_def show "n \<otimes> \<one> = n" by simp
next
  fix n m :: nat
  from mult_nat_def show "n \<otimes> m = m \<otimes> n" by simp
next
  fix k :: int
  from mult_int_def one_int_def show "k \<otimes> \<one> = k" by simp
next
  fix k l :: int
  from mult_int_def show "k \<otimes> l = l \<otimes> k" by simp
qed

instance * :: (monoid_comm, monoid_comm) monoid_comm
by default (simp_all add: split_paired_all mult_prod_def comm)

class group = monoidl +
  fixes inv :: "'a \<Rightarrow> 'a" ("\<div> _" [81] 80)
  assumes invl: "\<div> x \<otimes> x = \<one>"
begin

lemma cancel:
  "(x \<otimes> y = x \<otimes> z) = (y = z)"
proof
  fix x y z :: 'a
  assume eq: "x \<otimes> y = x \<otimes> z"
  hence "\<div> x \<otimes> (x \<otimes> y) = \<div> x \<otimes> (x \<otimes> z)" by simp
  with assoc have "\<div> x \<otimes> x \<otimes> y = \<div> x \<otimes> x \<otimes> z" by simp
  with neutl invl show "y = z" by simp
next
  fix x y z :: 'a
  assume eq: "y = z"
  thus "x \<otimes> y = x \<otimes> z" by simp
qed

subclass monoid
proof unfold_locales
  fix x
  from invl have "\<div> x \<otimes> x = \<one>" by simp
  with assoc [symmetric] neutl invl have "\<div> x \<otimes> (x \<otimes> \<one>) = \<div> x \<otimes> x" by simp
  with cancel show "x \<otimes> \<one> = x" by simp
qed

end context group begin

find_theorems name: neut

lemma invr:
  "x \<otimes> \<div> x = \<one>"
proof -
  from neutl invl have "\<div> x \<otimes> x \<otimes> \<div> x = \<div> x" by simp
  with neutr have "\<div> x \<otimes> x \<otimes> \<div> x = \<div> x \<otimes> \<one> " by simp
  with assoc have "\<div> x \<otimes> (x \<otimes> \<div> x) = \<div> x \<otimes> \<one> " by simp
  with cancel show ?thesis ..
qed

lemma all_inv [intro]:
  "(x\<Colon>'a) \<in> units"
  unfolding units_def
proof -
  fix x :: "'a"
  from invl invr have "\<div> x \<otimes> x = \<one>" and "x \<otimes> \<div> x = \<one>" . 
  then obtain y where "y \<otimes> x = \<one>" and "x \<otimes> y = \<one>" ..
  hence "\<exists>y\<Colon>'a. y \<otimes> x = \<one> \<and> x \<otimes> y = \<one>" by blast
  thus "x \<in> {y\<Colon>'a. \<exists>x\<Colon>'a. x \<otimes> y = \<one> \<and> y \<otimes> x = \<one>}" by simp
qed

lemma cancer:
  "(y \<otimes> x = z \<otimes> x) = (y = z)"
proof
  assume eq: "y \<otimes> x = z \<otimes> x"
  with assoc [symmetric] have "y \<otimes> (x \<otimes> \<div> x) = z \<otimes> (x \<otimes> \<div> x)" by (simp del: invr)
  with invr neutr show "y = z" by simp
next
  assume eq: "y = z"
  thus "y \<otimes> x = z \<otimes> x" by simp
qed

lemma inv_one:
  "\<div> \<one> = \<one>"
proof -
  from neutl have "\<div> \<one> = \<one> \<otimes> (\<div> \<one>)" ..
  moreover from invr have "... = \<one>" by simp
  finally show ?thesis .
qed

lemma inv_inv:
  "\<div> (\<div> x) = x"
proof -
  from invl invr neutr
    have "\<div> (\<div> x) \<otimes> \<div> x \<otimes> x = x \<otimes> \<div> x \<otimes> x" by simp
  with assoc [symmetric]
    have "\<div> (\<div> x) \<otimes> (\<div> x \<otimes> x) = x \<otimes> (\<div> x \<otimes> x)" by simp
  with invl neutr show ?thesis by simp
qed

lemma inv_mult_group:
  "\<div> (x \<otimes> y) = \<div> y \<otimes> \<div> x"
proof -
  from invl have "\<div> (x \<otimes> y) \<otimes> (x \<otimes> y) = \<one>" by simp
  with assoc have "\<div> (x \<otimes> y) \<otimes> x \<otimes> y = \<one>" by simp
  with neutl have "\<div> (x \<otimes> y) \<otimes> x \<otimes> y \<otimes> \<div> y \<otimes> \<div> x = \<div> y \<otimes> \<div> x" by simp
  with assoc have "\<div> (x \<otimes> y) \<otimes> (x \<otimes> (y \<otimes> \<div> y) \<otimes> \<div> x) = \<div> y \<otimes> \<div> x" by simp
  with invr neutr show ?thesis by simp
qed

lemma inv_comm:
  "x \<otimes> \<div> x = \<div> x \<otimes> x"
using invr invl by simp

definition
  pow :: "int \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "pow k x = (if k < 0 then \<div> (npow (nat (-k)) x)
    else (npow (nat k) x))"

abbreviation
  pow_syn :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infix "\<up>\<up>" 75)
where
  "x \<up>\<up> k \<equiv> pow k x"

lemma int_pow_zero:
  "x \<up>\<up> (0\<Colon>int) = \<one>"
using pow_def by simp

lemma int_pow_one:
  "\<one> \<up>\<up> (k\<Colon>int) = \<one>"
using pow_def nat_pow_one inv_one by simp

end

instance * :: (group, group) group
  inv_prod_def: "\<div> x \<equiv> let (x1, x2) = x in (\<div> x1, \<div> x2)"
by default (simp_all add: split_paired_all mult_prod_def one_prod_def inv_prod_def invl)

class group_comm = group + monoid_comm

instance int :: group_comm
  "\<div> k \<equiv> - (k\<Colon>int)"
proof
  fix k :: int
  from mult_int_def one_int_def inv_int_def show "\<div> k \<otimes> k = \<one>" by simp
qed

instance * :: (group_comm, group_comm) group_comm
by default (simp_all add: split_paired_all mult_prod_def comm)

definition
  "X a b c = (a \<otimes> \<one> \<otimes> b, a \<otimes> \<one> \<otimes> b, npow 3 [a, b] \<otimes> \<one> \<otimes> [a, b, c])"

definition
  "Y a b c = (a, \<div> a) \<otimes> \<one> \<otimes> \<div> (b, \<div> pow (-3) c)"

definition "x1 = X (1::nat) 2 3"
definition "x2 = X (1::int) 2 3"
definition "y2 = Y (1::int) 2 3"

export_code x1 x2 y2 pow in SML module_name Classpackage
  in OCaml file -
  in Haskell file -

end
