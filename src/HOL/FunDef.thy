(*  Title:      HOL/FunDef.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
*)

theory FunDef
imports Accessible_Part Datatype Recdef
uses 
("Tools/function_package/sum_tools.ML")
("Tools/function_package/fundef_common.ML")
("Tools/function_package/fundef_lib.ML")
("Tools/function_package/inductive_wrap.ML")
("Tools/function_package/context_tree.ML")
("Tools/function_package/fundef_prep.ML")
("Tools/function_package/fundef_proof.ML")
("Tools/function_package/termination.ML")
("Tools/function_package/mutual.ML")
("Tools/function_package/pattern_split.ML")
("Tools/function_package/fundef_package.ML")
("Tools/function_package/fundef_datatype.ML")
("Tools/function_package/auto_term.ML")
begin


definition
  THE_default :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a"
  "THE_default d P = (if (\<exists>!x. P x) then (THE x. P x) else d)"

lemma THE_defaultI': "\<exists>!x. P x \<Longrightarrow> P (THE_default d P)"
  by (simp add:theI' THE_default_def)

lemma THE_default1_equality: 
  "\<lbrakk>\<exists>!x. P x; P a\<rbrakk> \<Longrightarrow> THE_default d P = a"
  by (simp add:the1_equality THE_default_def)

lemma THE_default_none:
  "\<not>(\<exists>!x. P x) \<Longrightarrow> THE_default d P = d"
by (simp add:THE_default_def)


lemma fundef_ex1_existence:
assumes f_def: "f \<equiv> \<lambda>x. THE_default (d x) (\<lambda>y. (x,y)\<in>G)"
assumes ex1: "\<exists>!y. (x,y)\<in>G"
shows "(x, f x)\<in>G"
  by (simp only:f_def, rule THE_defaultI', rule ex1)

lemma fundef_ex1_uniqueness:
assumes f_def: "f \<equiv> \<lambda>x. THE_default (d x) (\<lambda>y. (x,y)\<in>G)"
assumes ex1: "\<exists>!y. (x,y)\<in>G"
assumes elm: "(x, h x)\<in>G"
shows "h x = f x"
  by (simp only:f_def, rule THE_default1_equality[symmetric], rule ex1, rule elm)

lemma fundef_ex1_iff:
assumes f_def: "f \<equiv> \<lambda>x. THE_default (d x) (\<lambda>y. (x,y)\<in>G)"
assumes ex1: "\<exists>!y. (x,y)\<in>G"
shows "((x, y)\<in>G) = (f x = y)"
  apply (auto simp:ex1 f_def THE_default1_equality)
  by (rule THE_defaultI', rule ex1)

lemma fundef_default_value:
assumes f_def: "f \<equiv> \<lambda>x. THE_default (d x) (\<lambda>y. (x,y)\<in>G)"
assumes graph: "\<And>x y. (x,y) \<in> G \<Longrightarrow> x \<in> D"
assumes "x \<notin> D"
shows "f x = d x"
proof -
  have "\<not>(\<exists>y. (x, y) \<in> G)"
  proof
    assume "(\<exists>y. (x, y) \<in> G)"
    with graph and `x\<notin>D` show False by blast
  qed
  hence "\<not>(\<exists>!y. (x, y) \<in> G)" by blast
  
  thus ?thesis
    unfolding f_def
    by (rule THE_default_none)
qed




subsection {* Projections *}
consts
  lpg::"(('a + 'b) * 'a) set"
  rpg::"(('a + 'b) * 'b) set"

inductive lpg
intros
  "(Inl x, x) : lpg"
inductive rpg
intros
  "(Inr y, y) : rpg"
definition
  "lproj x = (THE y. (x,y) : lpg)"
  "rproj x = (THE y. (x,y) : rpg)"

lemma lproj_inl:
  "lproj (Inl x) = x"
  by (auto simp:lproj_def intro: the_equality lpg.intros elim: lpg.cases)
lemma rproj_inr:
  "rproj (Inr x) = x"
  by (auto simp:rproj_def intro: the_equality rpg.intros elim: rpg.cases)




use "Tools/function_package/sum_tools.ML"
use "Tools/function_package/fundef_common.ML"
use "Tools/function_package/fundef_lib.ML"
use "Tools/function_package/inductive_wrap.ML"
use "Tools/function_package/context_tree.ML"
use "Tools/function_package/fundef_prep.ML"
use "Tools/function_package/fundef_proof.ML"
use "Tools/function_package/termination.ML"
use "Tools/function_package/mutual.ML"
use "Tools/function_package/pattern_split.ML"
use "Tools/function_package/fundef_package.ML"

setup FundefPackage.setup

use "Tools/function_package/fundef_datatype.ML"
setup FundefDatatype.setup

use "Tools/function_package/auto_term.ML"
setup FundefAutoTerm.setup


lemmas [fundef_cong] = 
  let_cong if_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong


lemma split_cong[fundef_cong]:
  "\<lbrakk> \<And>x y. (x, y) = q \<Longrightarrow> f x y = g x y; p = q \<rbrakk> 
  \<Longrightarrow> split f p = split g q"
  by (auto simp:split_def)


end
