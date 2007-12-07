(*  Title:      HOL/FunDef.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* General recursive function definitions *}

theory FunDef
imports Accessible_Part
uses
  ("Tools/function_package/fundef_lib.ML")
  ("Tools/function_package/fundef_common.ML")
  ("Tools/function_package/inductive_wrap.ML")
  ("Tools/function_package/context_tree.ML")
  ("Tools/function_package/fundef_core.ML")
  ("Tools/function_package/sum_tree.ML")
  ("Tools/function_package/mutual.ML")
  ("Tools/function_package/pattern_split.ML")
  ("Tools/function_package/fundef_package.ML")
  ("Tools/function_package/auto_term.ML")
  ("Tools/function_package/induction_scheme.ML")
begin

text {* Definitions with default value. *}

definition
  THE_default :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "THE_default d P = (if (\<exists>!x. P x) then (THE x. P x) else d)"

lemma THE_defaultI': "\<exists>!x. P x \<Longrightarrow> P (THE_default d P)"
  by (simp add: theI' THE_default_def)

lemma THE_default1_equality:
    "\<lbrakk>\<exists>!x. P x; P a\<rbrakk> \<Longrightarrow> THE_default d P = a"
  by (simp add: the1_equality THE_default_def)

lemma THE_default_none:
    "\<not>(\<exists>!x. P x) \<Longrightarrow> THE_default d P = d"
  by (simp add:THE_default_def)


lemma fundef_ex1_existence:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  shows "G x (f x)"
  apply (simp only: f_def)
  apply (rule THE_defaultI')
  apply (rule ex1)
  done

lemma fundef_ex1_uniqueness:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  assumes elm: "G x (h x)"
  shows "h x = f x"
  apply (simp only: f_def)
  apply (rule THE_default1_equality [symmetric])
   apply (rule ex1)
  apply (rule elm)
  done

lemma fundef_ex1_iff:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  shows "(G x y) = (f x = y)"
  apply (auto simp:ex1 f_def THE_default1_equality)
  apply (rule THE_defaultI')
  apply (rule ex1)
  done

lemma fundef_default_value:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes graph: "\<And>x y. G x y \<Longrightarrow> D x"
  assumes "\<not> D x"
  shows "f x = d x"
proof -
  have "\<not>(\<exists>y. G x y)"
  proof
    assume "\<exists>y. G x y"
    hence "D x" using graph ..
    with `\<not> D x` show False ..
  qed
  hence "\<not>(\<exists>!y. G x y)" by blast

  thus ?thesis
    unfolding f_def
    by (rule THE_default_none)
qed

definition in_rel_def[simp]:
  "in_rel R x y == (x, y) \<in> R"

lemma wf_in_rel:
  "wf R \<Longrightarrow> wfP (in_rel R)"
  by (simp add: wfP_def)


use "Tools/function_package/fundef_lib.ML"
use "Tools/function_package/fundef_common.ML"
use "Tools/function_package/inductive_wrap.ML"
use "Tools/function_package/context_tree.ML"
use "Tools/function_package/fundef_core.ML"
use "Tools/function_package/sum_tree.ML"
use "Tools/function_package/mutual.ML"
use "Tools/function_package/pattern_split.ML"
use "Tools/function_package/auto_term.ML"
use "Tools/function_package/fundef_package.ML"
use "Tools/function_package/induction_scheme.ML"

setup {* 
  FundefPackage.setup 
  #> InductionScheme.setup
*}

lemma let_cong [fundef_cong]:
  "M = N \<Longrightarrow> (\<And>x. x = N \<Longrightarrow> f x = g x) \<Longrightarrow> Let M f = Let N g"
  unfolding Let_def by blast

lemmas [fundef_cong] =
  if_cong image_cong INT_cong UN_cong
  bex_cong ball_cong imp_cong

lemma split_cong [fundef_cong]:
  "(\<And>x y. (x, y) = q \<Longrightarrow> f x y = g x y) \<Longrightarrow> p = q
    \<Longrightarrow> split f p = split g q"
  by (auto simp: split_def)

lemma comp_cong [fundef_cong]:
  "f (g x) = f' (g' x') \<Longrightarrow> (f o g) x = (f' o g') x'"
  unfolding o_apply .

end
