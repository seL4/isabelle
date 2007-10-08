(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Test and examples for Isar class package *}

theory Classpackage
imports List
begin

class semigroup = type +
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<^loc>\<otimes>" 70)
  assumes assoc: "x \<^loc>\<otimes> y \<^loc>\<otimes> z = x \<^loc>\<otimes> (y \<^loc>\<otimes> z)"

instance nat :: semigroup
  "m \<otimes> n \<equiv> m + n"
proof
  fix m n q :: nat 
  from mult_nat_def show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)" by simp
qed

instance int :: semigroup
  "k \<otimes> l \<equiv> k + l"
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
  fixes one :: 'a ("\<^loc>\<one>")
  assumes neutl: "\<^loc>\<one> \<^loc>\<otimes> x = x"

instance nat :: monoidl and int :: monoidl
  "\<one> \<equiv> 0"
  "\<one> \<equiv> 0"
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
  assumes neutr: "x \<^loc>\<otimes> \<^loc>\<one> = x"
begin

definition
  units :: "'a set" where
  "units = {y. \<exists>x. x \<^loc>\<otimes> y = \<^loc>\<one> \<and> y \<^loc>\<otimes> x = \<^loc>\<one>}"

lemma inv_obtain:
  assumes "x \<in> units"
  obtains y where "y \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> y = \<^loc>\<one>"
proof -
  from assms units_def obtain y
    where "y \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> y = \<^loc>\<one>" by auto
  thus ?thesis ..
qed

lemma inv_unique:
  assumes "y \<^loc>\<otimes> x = \<^loc>\<one>" "x \<^loc>\<otimes> y' = \<^loc>\<one>"
  shows "y = y'"
proof -
  from assms neutr have "y = y \<^loc>\<otimes> (x \<^loc>\<otimes> y')" by simp
  also with assoc have "... = (y \<^loc>\<otimes> x) \<^loc>\<otimes> y'" by simp
  also with assms neutl have "... = y'" by simp
  finally show ?thesis .
qed

lemma units_inv_comm:
  assumes inv: "x \<^loc>\<otimes> y = \<^loc>\<one>"
    and G: "x \<in> units"
  shows "y \<^loc>\<otimes> x = \<^loc>\<one>"
proof -
  from G inv_obtain obtain z
    where z_choice: "z \<^loc>\<otimes> x = \<^loc>\<one>" by blast
  from inv neutl neutr have "x \<^loc>\<otimes> y \<^loc>\<otimes> x = x \<^loc>\<otimes> \<^loc>\<one>" by simp
  with assoc have "z \<^loc>\<otimes> x \<^loc>\<otimes> y \<^loc>\<otimes> x = z \<^loc>\<otimes> x \<^loc>\<otimes> \<^loc>\<one>" by simp
  with neutl z_choice show ?thesis by simp
qed

fun
  npow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "npow 0 x = \<^loc>\<one>"
  | "npow (Suc n) x = x \<^loc>\<otimes> npow n x"

abbreviation
  npow_syn :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "\<^loc>\<up>" 75) where
  "x \<^loc>\<up> n \<equiv> npow n x"

lemma nat_pow_one:
  "\<^loc>\<one> \<^loc>\<up> n = \<^loc>\<one>"
using neutl by (induct n) simp_all

lemma nat_pow_mult: "x \<^loc>\<up> n \<^loc>\<otimes> x \<^loc>\<up> m = x \<^loc>\<up> (n + m)"
proof (induct n)
  case 0 with neutl show ?case by simp
next
  case (Suc n) with Suc.hyps assoc show ?case by simp
qed

lemma nat_pow_pow: "(x \<^loc>\<up> m) \<^loc>\<up> n = x \<^loc>\<up> (n * m)"
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
  assumes comm: "x \<^loc>\<otimes> y = y \<^loc>\<otimes> x"

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
  fixes inv :: "'a \<Rightarrow> 'a" ("\<^loc>\<div> _" [81] 80)
  assumes invl: "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>"
begin

lemma cancel:
  "(x \<^loc>\<otimes> y = x \<^loc>\<otimes> z) = (y = z)"
proof
  fix x y z :: 'a
  assume eq: "x \<^loc>\<otimes> y = x \<^loc>\<otimes> z"
  hence "\<^loc>\<div> x \<^loc>\<otimes> (x \<^loc>\<otimes> y) = \<^loc>\<div> x \<^loc>\<otimes> (x \<^loc>\<otimes> z)" by simp
  with assoc have "\<^loc>\<div> x \<^loc>\<otimes> x \<^loc>\<otimes> y = \<^loc>\<div> x \<^loc>\<otimes> x \<^loc>\<otimes> z" by simp
  with neutl invl show "y = z" by simp
next
  fix x y z :: 'a
  assume eq: "y = z"
  thus "x \<^loc>\<otimes> y = x \<^loc>\<otimes> z" by simp
qed

subclass monoid
proof unfold_locales
  fix x
  from invl have "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>" by simp
  with assoc [symmetric] neutl invl have "\<^loc>\<div> x \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<one>) = \<^loc>\<div> x \<^loc>\<otimes> x" by simp
  with cancel show "x \<^loc>\<otimes> \<^loc>\<one> = x" by simp
qed

end context group begin

find_theorems name: neut

lemma invr:
  "x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<one>"
proof -
  from neutl invl have "\<^loc>\<div> x \<^loc>\<otimes> x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> x" by simp
  with neutr have "\<^loc>\<div> x \<^loc>\<otimes> x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> x \<^loc>\<otimes> \<^loc>\<one> " by simp
  with assoc have "\<^loc>\<div> x \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<div> x) = \<^loc>\<div> x \<^loc>\<otimes> \<^loc>\<one> " by simp
  with cancel show ?thesis ..
qed

lemma all_inv [intro]:
  "(x\<Colon>'a) \<in> units"
  unfolding units_def
proof -
  fix x :: "'a"
  from invl invr have "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<one>" . 
  then obtain y where "y \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> y = \<^loc>\<one>" ..
  hence "\<exists>y\<Colon>'a. y \<^loc>\<otimes> x = \<^loc>\<one> \<and> x \<^loc>\<otimes> y = \<^loc>\<one>" by blast
  thus "x \<in> {y\<Colon>'a. \<exists>x\<Colon>'a. x \<^loc>\<otimes> y = \<^loc>\<one> \<and> y \<^loc>\<otimes> x = \<^loc>\<one>}" by simp
qed

lemma cancer:
  "(y \<^loc>\<otimes> x = z \<^loc>\<otimes> x) = (y = z)"
proof
  assume eq: "y \<^loc>\<otimes> x = z \<^loc>\<otimes> x"
  with assoc [symmetric] have "y \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<div> x) = z \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<div> x)" by (simp del: invr)
  with invr neutr show "y = z" by simp
next
  assume eq: "y = z"
  thus "y \<^loc>\<otimes> x = z \<^loc>\<otimes> x" by simp
qed

lemma inv_one:
  "\<^loc>\<div> \<^loc>\<one> = \<^loc>\<one>"
proof -
  from neutl have "\<^loc>\<div> \<^loc>\<one> = \<^loc>\<one> \<^loc>\<otimes> (\<^loc>\<div> \<^loc>\<one>)" ..
  moreover from invr have "... = \<^loc>\<one>" by simp
  finally show ?thesis .
qed

lemma inv_inv:
  "\<^loc>\<div> (\<^loc>\<div> x) = x"
proof -
  from invl invr neutr
    have "\<^loc>\<div> (\<^loc>\<div> x) \<^loc>\<otimes> \<^loc>\<div> x \<^loc>\<otimes> x = x \<^loc>\<otimes> \<^loc>\<div> x \<^loc>\<otimes> x" by simp
  with assoc [symmetric]
    have "\<^loc>\<div> (\<^loc>\<div> x) \<^loc>\<otimes> (\<^loc>\<div> x \<^loc>\<otimes> x) = x \<^loc>\<otimes> (\<^loc>\<div> x \<^loc>\<otimes> x)" by simp
  with invl neutr show ?thesis by simp
qed

lemma inv_mult_group:
  "\<^loc>\<div> (x \<^loc>\<otimes> y) = \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x"
proof -
  from invl have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> (x \<^loc>\<otimes> y) = \<^loc>\<one>" by simp
  with assoc have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> x \<^loc>\<otimes> y = \<^loc>\<one>" by simp
  with neutl have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> x \<^loc>\<otimes> y \<^loc>\<otimes> \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x" by simp
  with assoc have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> (x \<^loc>\<otimes> (y \<^loc>\<otimes> \<^loc>\<div> y) \<^loc>\<otimes> \<^loc>\<div> x) = \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x" by simp
  with invr neutr show ?thesis by simp
qed

lemma inv_comm:
  "x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> x \<^loc>\<otimes> x"
using invr invl by simp

definition
  pow :: "int \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "pow k x = (if k < 0 then \<^loc>\<div> (npow (nat (-k)) x)
    else (npow (nat k) x))"

abbreviation
  pow_syn :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infix "\<^loc>\<up>\<up>" 75)
where
  "x \<^loc>\<up>\<up> k \<equiv> pow k x"

lemma int_pow_zero:
  "x \<^loc>\<up>\<up> (0\<Colon>int) = \<^loc>\<one>"
using pow_def by simp

lemma int_pow_one:
  "\<^loc>\<one> \<^loc>\<up>\<up> (k\<Colon>int) = \<^loc>\<one>"
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
