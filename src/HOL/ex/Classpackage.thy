(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Test and Examples for Pure/Tools/class_package.ML *}

theory Classpackage
imports Main
begin

class semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<^loc>\<otimes>" 70)
  assumes assoc: "x \<^loc>\<otimes> y \<^loc>\<otimes> z = x \<^loc>\<otimes> (y \<^loc>\<otimes> z)"

instance nat :: semigroup
  "m \<otimes> n \<equiv> m + n"
proof
  fix m n q :: nat 
  from semigroup_nat_def show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)" by simp
qed

instance int :: semigroup
  "k \<otimes> l \<equiv> k + l"
proof
  fix k l j :: int
  from semigroup_int_def show "k \<otimes> l \<otimes> j = k \<otimes> (l \<otimes> j)" by simp
qed

instance list :: (type) semigroup
  "xs \<otimes> ys \<equiv> xs @ ys"
proof
  fix xs ys zs :: "'a list"
  show "xs \<otimes> ys \<otimes> zs = xs \<otimes> (ys \<otimes> zs)"
  proof -
    from semigroup_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
    thus ?thesis by simp
  qed
qed

class monoidl = semigroup +
  fixes one :: 'a ("\<^loc>\<one>")
  assumes neutl: "\<^loc>\<one> \<^loc>\<otimes> x = x"

instance monoidl_num_def: nat :: monoidl and int :: monoidl
  "\<one> \<equiv> 0"
  "\<one> \<equiv> 0"
proof
  fix n :: nat
  from monoidl_num_def show "\<one> \<otimes> n = n" by simp
next
  fix k :: int
  from monoidl_num_def show "\<one> \<otimes> k = k" by simp
qed

instance list :: (type) monoidl
  "\<one> \<equiv> []"
proof
  fix xs :: "'a list"
  show "\<one> \<otimes> xs = xs"
  proof -
    from mult_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
    moreover from monoidl_list_def have "\<one> \<equiv> []\<Colon>'a list" by simp
    ultimately show ?thesis by simp
  qed
qed  

class monoid = monoidl +
  assumes neutr: "x \<^loc>\<otimes> \<^loc>\<one> = x"

instance monoid_list_def: list :: (type) monoid
proof
  fix xs :: "'a list"
  show "xs \<otimes> \<one> = xs"
  proof -
    from mult_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
    moreover from monoid_list_def have "\<one> \<equiv> []\<Colon>'a list" by simp
    ultimately show ?thesis by simp
  qed
qed  

class monoid_comm = monoid +
  assumes comm: "x \<^loc>\<otimes> y = y \<^loc>\<otimes> x"

instance monoid_comm_num_def: nat :: monoid_comm and int :: monoid_comm
proof
  fix n :: nat
  from monoid_comm_num_def show "n \<otimes> \<one> = n" by simp
next
  fix n m :: nat
  from monoid_comm_num_def show "n \<otimes> m = m \<otimes> n" by simp
next
  fix k :: int
  from monoid_comm_num_def show "k \<otimes> \<one> = k" by simp
next
  fix k l :: int
  from monoid_comm_num_def show "k \<otimes> l = l \<otimes> k" by simp
qed

definition (in monoid)
  units :: "'a set" where
  "units = { y. \<exists>x. x \<^loc>\<otimes> y = \<^loc>\<one> \<and> y \<^loc>\<otimes> x = \<^loc>\<one> }"

lemma (in monoid) inv_obtain:
  assumes ass: "x \<in> units"
  obtains y where "y \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> y = \<^loc>\<one>"
proof -
  from ass units_def obtain y
    where "y \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> y = \<^loc>\<one>" by auto
  thus ?thesis ..
qed

lemma (in monoid) inv_unique:
  assumes eq: "y \<^loc>\<otimes> x = \<^loc>\<one>" "x \<^loc>\<otimes> y' = \<^loc>\<one>"
  shows "y = y'"
proof -
  from eq neutr have "y = y \<^loc>\<otimes> (x \<^loc>\<otimes> y')" by simp
  also with assoc have "... = (y \<^loc>\<otimes> x) \<^loc>\<otimes> y'" by simp
  also with eq neutl have "... = y'" by simp
  finally show ?thesis .
qed

lemma (in monoid) units_inv_comm:
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

consts
  reduce :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"

primrec
  "reduce f g 0 x = g"
  "reduce f g (Suc n) x = f x (reduce f g n x)"

definition (in monoid)
  npow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  npow_def_prim: "npow n x = reduce (op \<^loc>\<otimes>) \<^loc>\<one> n x"

abbreviation (in monoid)
  abbrev_npow :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "\<^loc>\<up>" 75) where
  "x \<^loc>\<up> n \<equiv> npow n x"

lemma (in monoid) npow_def:
  "x \<^loc>\<up> 0 = \<^loc>\<one>"
  "x \<^loc>\<up> Suc n = x \<^loc>\<otimes> x \<^loc>\<up> n"
using npow_def_prim by simp_all

lemma (in monoid) nat_pow_one:
  "\<^loc>\<one> \<^loc>\<up> n = \<^loc>\<one>"
using npow_def neutl by (induct n) simp_all

lemma (in monoid) nat_pow_mult:
  "npow n x \<^loc>\<otimes> npow m x = npow (n + m) x"
proof (induct n)
  case 0 with neutl npow_def show ?case by simp
next
  case (Suc n) with Suc.hyps assoc npow_def show ?case by simp
qed

lemma (in monoid) nat_pow_pow:
  "npow n (npow m x) = npow (n * m) x"
using npow_def nat_pow_mult by (induct n) simp_all

class group = monoidl +
  fixes inv :: "'a \<Rightarrow> 'a" ("\<^loc>\<div> _" [81] 80)
  assumes invl: "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>"

class group_comm = group + monoid_comm

instance group_comm_int_def: int :: group_comm
  "\<div> k \<equiv> - (k\<Colon>int)"
proof
  fix k :: int
  from group_comm_int_def show "\<div> k \<otimes> k = \<one>" by simp
qed

lemma (in group) cancel:
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

lemma (in group) neutr:
  "x \<^loc>\<otimes> \<^loc>\<one> = x"
proof -
  from invl have "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>" by simp
  with assoc [symmetric] neutl invl have "\<^loc>\<div> x \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<one>) = \<^loc>\<div> x \<^loc>\<otimes> x" by simp
  with cancel show ?thesis by simp
qed

lemma (in group) invr:
  "x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<one>"
proof -
  from neutl invl have "\<^loc>\<div> x \<^loc>\<otimes> x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> x" by simp
  with neutr have "\<^loc>\<div> x \<^loc>\<otimes> x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> x \<^loc>\<otimes> \<^loc>\<one> " by simp
  with assoc have "\<^loc>\<div> x \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<div> x) = \<^loc>\<div> x \<^loc>\<otimes> \<^loc>\<one> " by simp
  with cancel show ?thesis ..
qed

instance group < monoid
proof -
  fix x
  from neutr show "x \<^loc>\<otimes> \<^loc>\<one> = x" .
qed

lemma (in group) all_inv [intro]:
  "(x\<Colon>'a) \<in> monoid.units (op \<^loc>\<otimes>) \<^loc>\<one>"
  unfolding units_def
proof -
  fix x :: "'a"
  from invl invr have "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<one>" . 
  then obtain y where "y \<^loc>\<otimes> x = \<^loc>\<one>" and "x \<^loc>\<otimes> y = \<^loc>\<one>" ..
  hence "\<exists>y\<Colon>'a. y \<^loc>\<otimes> x = \<^loc>\<one> \<and> x \<^loc>\<otimes> y = \<^loc>\<one>" by blast
  thus "x \<in> {y\<Colon>'a. \<exists>x\<Colon>'a. x \<^loc>\<otimes> y = \<^loc>\<one> \<and> y \<^loc>\<otimes> x = \<^loc>\<one>}" by simp
qed

lemma (in group) cancer:
  "(y \<^loc>\<otimes> x = z \<^loc>\<otimes> x) = (y = z)"
proof
  assume eq: "y \<^loc>\<otimes> x = z \<^loc>\<otimes> x"
  with assoc [symmetric] have "y \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<div> x) = z \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<div> x)" by (simp del: invr)
  with invr neutr show "y = z" by simp
next
  assume eq: "y = z"
  thus "y \<^loc>\<otimes> x = z \<^loc>\<otimes> x" by simp
qed

lemma (in group) inv_one:
  "\<^loc>\<div> \<^loc>\<one> = \<^loc>\<one>"
proof -
  from neutl have "\<^loc>\<div> \<^loc>\<one> = \<^loc>\<one> \<^loc>\<otimes> (\<^loc>\<div> \<^loc>\<one>)" ..
  moreover from invr have "... = \<^loc>\<one>" by simp
  finally show ?thesis .
qed

lemma (in group) inv_inv:
  "\<^loc>\<div> (\<^loc>\<div> x) = x"
proof -
  from invl invr neutr
    have "\<^loc>\<div> (\<^loc>\<div> x) \<^loc>\<otimes> \<^loc>\<div> x \<^loc>\<otimes> x = x \<^loc>\<otimes> \<^loc>\<div> x \<^loc>\<otimes> x" by simp
  with assoc [symmetric]
    have "\<^loc>\<div> (\<^loc>\<div> x) \<^loc>\<otimes> (\<^loc>\<div> x \<^loc>\<otimes> x) = x \<^loc>\<otimes> (\<^loc>\<div> x \<^loc>\<otimes> x)" by simp
  with invl neutr show ?thesis by simp
qed

lemma (in group) inv_mult_group:
  "\<^loc>\<div> (x \<^loc>\<otimes> y) = \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x"
proof -
  from invl have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> (x \<^loc>\<otimes> y) = \<^loc>\<one>" by simp
  with assoc have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> x \<^loc>\<otimes> y = \<^loc>\<one>" by simp
  with neutl have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> x \<^loc>\<otimes> y \<^loc>\<otimes> \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x" by simp
  with assoc have "\<^loc>\<div> (x \<^loc>\<otimes> y) \<^loc>\<otimes> (x \<^loc>\<otimes> (y \<^loc>\<otimes> \<^loc>\<div> y) \<^loc>\<otimes> \<^loc>\<div> x) = \<^loc>\<div> y \<^loc>\<otimes> \<^loc>\<div> x" by simp
  with invr neutr show ?thesis by simp
qed

lemma (in group) inv_comm:
  "x \<^loc>\<otimes> \<^loc>\<div> x = \<^loc>\<div> x \<^loc>\<otimes> x"
using invr invl by simp

definition (in group)
  pow :: "int \<Rightarrow> 'a \<Rightarrow> 'a" where
  "pow k x = (if k < 0 then \<^loc>\<div> (monoid.npow (op \<^loc>\<otimes>) \<^loc>\<one> (nat (-k)) x)
    else (monoid.npow (op \<^loc>\<otimes>) \<^loc>\<one> (nat k) x))"

abbreviation (in group)
  abbrev_pow :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infix "\<^loc>\<up>" 75) where
  "x \<^loc>\<up> k \<equiv> pow k x"

lemma (in group) int_pow_zero:
  "x \<^loc>\<up> (0\<Colon>int) = \<^loc>\<one>"
using npow_def pow_def by simp

lemma (in group) int_pow_one:
  "\<^loc>\<one> \<^loc>\<up> (k\<Colon>int) = \<^loc>\<one>"
using pow_def nat_pow_one inv_one by simp

instance semigroup_prod_def: * :: (semigroup, semigroup) semigroup
  mult_prod_def: "x \<otimes> y \<equiv> let (x1, x2) = x; (y1, y2) = y in
              (x1 \<otimes> y1, x2 \<otimes> y2)"
by default (simp_all add: split_paired_all semigroup_prod_def assoc)

instance monoidl_prod_def: * :: (monoidl, monoidl) monoidl
  one_prod_def: "\<one> \<equiv> (\<one>, \<one>)"
by default (simp_all add: split_paired_all monoidl_prod_def neutl)

instance monoid_prod_def: * :: (monoid, monoid) monoid
by default (simp_all add: split_paired_all monoid_prod_def neutr)

instance monoid_comm_prod_def: * :: (monoid_comm, monoid_comm) monoid_comm
by default (simp_all add: split_paired_all monoidl_prod_def comm)

instance group_prod_def: * :: (group, group) group
  inv_prod_def: "\<div> x \<equiv> let (x1, x2) = x in (\<div> x1, \<div> x2)"
by default (simp_all add: split_paired_all group_prod_def invl)

instance group_comm_prod_def: * :: (group_comm, group_comm) group_comm
by default (simp_all add: split_paired_all group_prod_def comm)

definition
  "X a b c = (a \<otimes> \<one> \<otimes> b, a \<otimes> \<one> \<otimes> b, [a, b] \<otimes> \<one> \<otimes> [a, b, c])"
definition
  "Y a b c = (a, \<div> a) \<otimes> \<one> \<otimes> \<div> (b, \<div> c)"

definition "x1 = X (1::nat) 2 3"
definition "x2 = X (1::int) 2 3"
definition "y2 = Y (1::int) 2 3"

code_gen "op \<otimes>" \<one> inv
code_gen X Y (SML *) (Haskell -)
code_gen x1 x2 y2 (SML *) (Haskell -)

end
