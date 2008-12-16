(*  Title:      StateSpaceLocale.thy
    ID:         $Id$
    Author:     Norbert Schirmer, TU Muenchen
*)

header {* Setup for State Space Locales \label{sec:StateSpaceLocale}*}

theory StateSpaceLocale imports StateFun 
uses "state_space.ML" "state_fun.ML"
begin

setup StateFun.setup

text {* For every type that is to be stored in a state space, an
instance of this locale is imported in order convert the abstract and
concrete values.*}


class_locale project_inject =
 fixes project :: "'value \<Rightarrow> 'a"
 and   "inject":: "'a \<Rightarrow> 'value"
 assumes project_inject_cancel [statefun_simp]: "project (inject x) = x"

lemma (in project_inject)
 ex_project [statefun_simp]: "\<exists>v. project v = x"
  apply (rule_tac x= "inject x" in exI)
  apply (simp add: project_inject_cancel)
  done

lemma (in project_inject)
 project_inject_comp_id [statefun_simp]: "project \<circ> inject = id"
  by (rule ext) (simp add: project_inject_cancel)

lemma (in project_inject)
 project_inject_comp_cancel[statefun_simp]: "f \<circ> project \<circ> inject = f"
  by (rule ext) (simp add: project_inject_cancel)



end