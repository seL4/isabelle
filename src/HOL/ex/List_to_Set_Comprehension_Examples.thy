(*  Title:      HOL/ex/List_to_Set_Comprehension_Examples.thy
    Author:     Lukas Bulwahn
    Copyright   2011 TU Muenchen
*)

section {* Examples for the list comprehension to set comprehension simproc *}

theory List_to_Set_Comprehension_Examples
imports Main
begin

text {*
Examples that show and test the simproc that rewrites list comprehensions
applied to List.set to set comprehensions.
*}

subsection {* Some own examples for set (case ..) simpproc *}

lemma "set [(x, xs). x # xs <- as] = {(x, xs). x # xs \<in> set as}"
by auto

lemma "set [(x, y, ys). x # y # ys <- as] = {(x, y, ys). x # y # ys \<in> set as}"
by auto

lemma "set [(x, y, z, zs). x # y # z # zs <- as] = {(x, y, z, zs). x # y # z # zs \<in> set as}"
by auto

lemma "set [(zs, x, z, y). x # (y, z) # zs <- as] = {(zs, x, z, y). x # (y, z) # zs \<in> set as}" 
by auto

lemma "set [(x, y). x # y <- zs, x = x'] = {(x, y). x # y \<in> set zs & x = x'}"
by auto

subsection {* Existing examples from the List theory *}

lemma "set [(x,y,z). b] = {(x', y', z'). x = x' & y = y' & z = z' & b}"
by auto

lemma "set [(x,y,z). x\<leftarrow>xs] = {(x, y', z'). x \<in> set xs & y' = y & z = z'}"
by auto

lemma "set [e x y. x\<leftarrow>xs, y\<leftarrow>ys] = {z. \<exists> x y. z = e x y & x \<in> set xs & y \<in> set ys}"
by auto

lemma "set [(x,y,z). x<a, x>b] = {(x', y', z'). x' = x & y' = y & z = z' & x < a & x>b}"
by auto

lemma "set [(x,y,z). x\<leftarrow>xs, x>b] = {(x', y', z'). y = y' & z = z' & x' \<in> set xs & x' > b}"
by auto

lemma "set [(x,y,z). x<a, x\<leftarrow>xs] = {(x', y', z'). y = y' & z = z' & x' \<in> set xs & x < a}"
by auto

lemma "set [(x,y). Cons True x \<leftarrow> xs] = {(x, y'). y = y' & Cons True x \<in> set xs}"
by auto

lemma "set [(x,y,z). Cons x [] \<leftarrow> xs] = {(x, y', z'). y = y' & z = z' & Cons x [] \<in> set xs}"
by auto

lemma "set [(x,y,z). x<a, x>b, x=d] = {(x', y', z'). x = x' & y = y' & z = z' & x < a & x > b & x = d}"
by auto

lemma "set [(x,y,z). x<a, x>b, y\<leftarrow>ys] = {(x', y, z'). x = x' & y \<in> set ys & z = z' & x < a & x > b}"
by auto

lemma "set [(x,y,z). x<a, x\<leftarrow>xs,y>b] = {(x',y',z'). x' \<in> set xs & y = y' & z = z' & x < a & y > b}"
by auto

lemma "set [(x,y,z). x<a, x\<leftarrow>xs, y\<leftarrow>ys] = {(x', y', z'). z = z' & x < a & x' \<in> set xs & y' \<in> set ys}"
by auto

lemma "set [(x,y,z). x\<leftarrow>xs, x>b, y<a] = {(x', y', z'). y = y' & z = z' & x' \<in> set xs & x' > b & y < a}"
by auto

lemma "set [(x,y,z). x\<leftarrow>xs, x>b, y\<leftarrow>ys] = {(x', y', z'). z = z' & x' \<in> set xs & x' > b & y' \<in> set ys}"
by auto

lemma "set [(x,y,z). x\<leftarrow>xs, y\<leftarrow>ys,y>x] = {(x', y', z'). z = z' & x' \<in> set xs & y' \<in> set ys & y' > x'}"
by auto

lemma "set [(x,y,z). x\<leftarrow>xs, y\<leftarrow>ys,z\<leftarrow>zs] = {(x', y', z'). x' \<in> set xs & y' \<in> set ys & z' \<in> set zs}"
by auto

end
