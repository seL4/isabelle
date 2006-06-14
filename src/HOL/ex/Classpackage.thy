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
  "m \<otimes> n == (m::nat) + n"
proof
  fix m n q :: nat 
  from semigroup_nat_def show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)" by simp
qed

instance int :: semigroup
  "k \<otimes> l == (k::int) + l"
proof
  fix k l j :: int
  from semigroup_int_def show "k \<otimes> l \<otimes> j = k \<otimes> (l \<otimes> j)" by simp
qed

instance (type) list :: semigroup
  "xs \<otimes> ys == xs @ ys"
proof
  fix xs ys zs :: "'a list"
  show "xs \<otimes> ys \<otimes> zs = xs \<otimes> (ys \<otimes> zs)"
  proof -
    from semigroup_list_def have "\<And>xs ys::'a list. xs \<otimes> ys == xs @ ys".
    thus ?thesis by simp
  qed
qed

class monoidl = semigroup +
  fixes one :: 'a ("\<^loc>\<one>")
  assumes neutl: "\<^loc>\<one> \<^loc>\<otimes> x = x"

instance nat :: monoidl
  "\<one> == (0::nat)"
proof
  fix n :: nat
  from semigroup_nat_def monoidl_nat_def show "\<one> \<otimes> n = n" by simp
qed

instance int :: monoidl
  "\<one> == (0::int)"
proof
  fix k :: int
  from semigroup_int_def monoidl_int_def show "\<one> \<otimes> k = k" by simp
qed

instance (type) list :: monoidl
  "\<one> == []"
proof
  fix xs :: "'a list"
  show "\<one> \<otimes> xs = xs"
  proof -
    from semigroup_list_def have "\<And>xs ys::'a list. xs \<otimes> ys == xs @ ys".
    moreover from monoidl_list_def have "\<one> == []::'a list".
    ultimately show ?thesis by simp
  qed
qed  

class monoid = monoidl +
  assumes neutr: "x \<^loc>\<otimes> \<^loc>\<one> = x"

instance (type) list :: monoid
proof
  fix xs :: "'a list"
  show "xs \<otimes> \<one> = xs"
  proof -
    from semigroup_list_def have "\<And>xs ys::'a list. xs \<otimes> ys == xs @ ys".
    moreover from monoidl_list_def have "\<one> == []::'a list".
    ultimately show ?thesis by simp
  qed
qed  

class monoid_comm = monoid +
  assumes comm: "x \<^loc>\<otimes> y = y \<^loc>\<otimes> x"

instance nat :: monoid_comm
proof
  fix n :: nat
  from semigroup_nat_def monoidl_nat_def show "n \<otimes> \<one> = n" by simp
next
  fix n m :: nat
  from semigroup_nat_def monoidl_nat_def show "n \<otimes> m = m \<otimes> n" by simp
qed

instance int :: monoid_comm
proof
  fix k :: int
  from semigroup_int_def monoidl_int_def show "k \<otimes> \<one> = k" by simp
next
  fix k l :: int
  from semigroup_int_def monoidl_int_def show "k \<otimes> l = l \<otimes> k" by simp
qed

definition (in monoid)
  units :: "'a set"
  units_def: "units = { y. \<exists>x. x \<^loc>\<otimes> y = \<^loc>\<one> \<and> y \<^loc>\<otimes> x = \<^loc>\<one> }"

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
  npow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  npow_def_prim: "npow n x = reduce (op \<^loc>\<otimes>) \<^loc>\<one> n x"

abbreviation (in monoid)
  abbrev_npow :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "\<^loc>\<up>" 75)
  "x \<^loc>\<up> n == npow n x"

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
  case (Suc n) with prems assoc npow_def show ?case by simp
qed

lemma (in monoid) nat_pow_pow:
  "npow n (npow m x) = npow (n * m) x"
using npow_def nat_pow_mult by (induct n) simp_all

class group = monoidl +
  fixes inv :: "'a \<Rightarrow> 'a" ("\<^loc>\<div> _" [81] 80)
  assumes invl: "\<^loc>\<div> x \<^loc>\<otimes> x = \<^loc>\<one>"

class group_comm = group + monoid_comm

instance int :: group_comm
  "\<div> k == - (k::int)"
proof
  fix k :: int
  from semigroup_int_def monoidl_int_def group_comm_int_def show "\<div> k \<otimes> k = \<one>" by simp
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

interpretation group < monoid
proof
  fix x :: "'a"
  from neutr show "x \<^loc>\<otimes> \<^loc>\<one> = x" .
qed

instance group < monoid
proof
  fix x :: "'a::group"
  from group.mult_one.neutr [standard] show "x \<otimes> \<one> = x" .
qed

lemma (in group) all_inv [intro]:
  "(x::'a) \<in> monoid.units (op \<^loc>\<otimes>) \<^loc>\<one>"
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
  pow :: "int \<Rightarrow> 'a \<Rightarrow> 'a"
  pow_def: "pow k x = (if k < 0 then \<^loc>\<div> (monoid.npow (op \<^loc>\<otimes>) \<^loc>\<one> (nat (-k)) x)
    else (monoid.npow (op \<^loc>\<otimes>) \<^loc>\<one> (nat k) x))"

abbreviation (in group)
  abbrev_pow :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infix "\<^loc>\<up>" 75)
  "x \<^loc>\<up> k == pow k x"

lemma (in group) int_pow_zero:
  "x \<^loc>\<up> (0::int) = \<^loc>\<one>"
using npow_def pow_def by simp

lemma (in group) int_pow_one:
  "\<^loc>\<one> \<^loc>\<up> (k::int) = \<^loc>\<one>"
using pow_def nat_pow_one inv_one by simp

instance group_prod_def: (group, group) * :: group
  mult_prod_def: "x \<otimes> y == let (x1, x2) = x in (let (y1, y2) = y in
              ((x1::'a::group) \<otimes> y1, (x2::'b::group) \<otimes> y2))"
  mult_one_def: "\<one> == (\<one>::'a::group, \<one>::'b::group)"
  mult_inv_def: "\<div> x == let (x1, x2) = x in (\<div> x1, \<div> x2)"
by default (simp_all add: split_paired_all group_prod_def semigroup.assoc monoidl.neutl group.invl)

instance group_comm_prod_def: (group_comm, group_comm) * :: group_comm
by default (simp_all add: split_paired_all group_prod_def semigroup.assoc monoidl.neutl group.invl monoid_comm.comm)

definition
  "x = ((2::nat) \<otimes> \<one> \<otimes> 3, (2::int) \<otimes> \<one> \<otimes> \<div> 3, [1::nat, 2] \<otimes> \<one> \<otimes> [1, 2, 3])"
  "y = (2 :: int, \<div> 2 :: int) \<otimes> \<one> \<otimes> (3, \<div> 3)"

code_generate (ml, haskell) "op \<otimes>" "\<one>" "inv"
code_generate (ml, haskell) x
code_generate (ml, haskell) y

code_serialize ml (-)

end
