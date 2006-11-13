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
(*("Tools/function_package/fundef_datatype.ML")*)
("Tools/function_package/auto_term.ML")
begin

section {* Wellfoundedness and Accessibility: Predicate versions *}


constdefs
  wfP         :: "('a \<Rightarrow> 'a \<Rightarrow> bool) => bool"
  "wfP(r) == (!P. (!x. (!y. r y x --> P(y)) --> P(x)) --> (!x. P(x)))"

lemma wfP_induct: 
    "[| wfP r;           
        !!x.[| ALL y. r y x --> P(y) |] ==> P(x)  
     |]  ==>  P(a)"
by (unfold wfP_def, blast)

lemmas wfP_induct_rule = wfP_induct [rule_format, consumes 1, case_names less]

definition in_rel_def[simp]:
  "in_rel R x y == (x, y) \<in> R"

lemma wf_in_rel:
  "wf R \<Longrightarrow> wfP (in_rel R)"
  unfolding wfP_def wf_def in_rel_def .


inductive2 accP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
intros
    accPI: "(!!y. r y x ==> accP r y) ==> accP r x"


theorem accP_induct:
  assumes major: "accP r a"
  assumes hyp: "!!x. accP r x ==> \<forall>y. r y x --> P y ==> P x"
  shows "P a"
  apply (rule major [THEN accP.induct])
  apply (rule hyp)
   apply (rule accPI)
   apply fast
  apply fast
  done

theorems accP_induct_rule = accP_induct [rule_format, induct set: accP]

theorem accP_downward: "accP r b ==> r a b ==> accP r a"
  apply (erule accP.cases)
  apply fast
  done


lemma accP_subset:
  assumes sub: "\<And>x y. R1 x y \<Longrightarrow> R2 x y"
  shows "\<And>x. accP R2 x \<Longrightarrow> accP R1 x"
proof-
  fix x assume "accP R2 x"
  then show "accP R1 x"
  proof (induct x)
    fix x
    assume ih: "\<And>y. R2 y x \<Longrightarrow> accP R1 y"
    with sub show "accP R1 x"
      by (blast intro:accPI)
  qed
qed


lemma accP_subset_induct:
  assumes subset: "\<And>x. D x \<Longrightarrow> accP R x"
    and dcl: "\<And>x z. \<lbrakk>D x; R z x\<rbrakk> \<Longrightarrow> D z"
    and "D x"
    and istep: "\<And>x. \<lbrakk>D x; (\<And>z. R z x \<Longrightarrow> P z)\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof -
  from subset and `D x` 
  have "accP R x" .
  then show "P x" using `D x`
  proof (induct x)
    fix x
    assume "D x"
      and "\<And>y. R y x \<Longrightarrow> D y \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed


section {* Definitions with default value *}

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
assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
assumes ex1: "\<exists>!y. G x y"
shows "G x (f x)"
  by (simp only:f_def, rule THE_defaultI', rule ex1)





lemma fundef_ex1_uniqueness:
assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
assumes ex1: "\<exists>!y. G x y"
assumes elm: "G x (h x)"
shows "h x = f x"
  by (simp only:f_def, rule THE_default1_equality[symmetric], rule ex1, rule elm)

lemma fundef_ex1_iff:
assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
assumes ex1: "\<exists>!y. G x y"
shows "(G x y) = (f x = y)"
  apply (auto simp:ex1 f_def THE_default1_equality)
  by (rule THE_defaultI', rule ex1)

lemma fundef_default_value:
assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
assumes graph: "\<And>x y. G x y \<Longrightarrow> x \<in> D"
assumes "x \<notin> D"
shows "f x = d x"
proof -
  have "\<not>(\<exists>y. G x y)"
  proof
    assume "(\<exists>y. G x y)"
    with graph and `x\<notin>D` show False by blast
  qed
  hence "\<not>(\<exists>!y. G x y)" by blast
  
  thus ?thesis
    unfolding f_def
    by (rule THE_default_none)
qed



section {* Projections *}
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
use "Tools/function_package/auto_term.ML"
use "Tools/function_package/fundef_package.ML"

setup FundefPackage.setup

lemmas [fundef_cong] = 
  let_cong if_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong


lemma split_cong[fundef_cong]:
  "\<lbrakk> \<And>x y. (x, y) = q \<Longrightarrow> f x y = g x y; p = q \<rbrakk> 
  \<Longrightarrow> split f p = split g q"
  by (auto simp:split_def)


end
